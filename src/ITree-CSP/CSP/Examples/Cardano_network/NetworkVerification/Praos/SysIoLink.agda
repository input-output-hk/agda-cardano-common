{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 — io-peel layer (item 6), NEW small module importing the
-- cached `SysOracle` interface (cheap deserialisation, no re-elaboration).
-- STEP 1 here: the LeiosFetch bundle io-link pins, mirroring the committed
-- KA/TS/LN link-pins in `SysOracle`.  Later steps (nodeX-ev-io / io
-- disjointness / top-nodes-io) land in this module too.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink (blkA : Block₃) where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (⊤ to ⊤₀)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Maybe.Properties using (just-injective)
open import Process_Trees using (PTree; ExtI; react; ret; react-injective)

-- links, api alphabet, block payloads
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; Block₃; produce )
open import CSP.Examples.Cardano_network.Net p using
  ( Net; Net-≟; Net_Api; Net_Api-≟; apiCS; apiBF; input; output; done; break; Link
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack; apiKA; apiTS; apiLN; apiLF
  -- the producer/consumer api tags (the role discriminator's index values)
  ; reqCSRequestNext; sendCSAwaitReply; sendCSRollForward
  ; sendCSRequestNext; recvCSRollforward; sendCSDone
  -- extra CS api tags used as patterns in the item-3a io-role clauses
  ; sendCSFindIntersect; sendCSRollBackward; sendCSIntersectFound; sendCSIntersectNotFound
  ; recvCSRollback; recvCSIntersectFound; recvCSIntersectNotFound; reqCSFindIntersect
  ; reqBFRange; sendBFStartBatch; sendBFBlock; sendBFBatchDone; sendBFNoBlocks
  ; sendBFRequestRange; recvBFBlock; sendBFClientDone )
open import CSP.Examples.Cardano_network.Data p using ( Payload; DecEq-ChainRange )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi; IDs
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
  ; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetworkPar p using
  ( ιCS; ιBF; ιLF
  ; KAclientA; KAserverA; TSclientA; TSserverA
  ; LNclientA; LNserverA; LFclientA; LFserverA )
import CSP.Examples.Cardano_network.ChainSync  p as CS
import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Examples.Cardano_network.KeepAlive  p as KA
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.LeiosNotify p as LNp
import CSP.Examples.Cardano_network.LeiosFetch  p as LFp
import Semantics.LTS {E = CS.CSEv} {I = ExtI CS.CSEv} as CSL
import Semantics.LTS {E = BF.BFEv} {I = ExtI BF.BFEv} as BFL
import Semantics.LTS {E = KA.KAEv} {I = ExtI KA.KAEv} as KAL
import Semantics.LTS {E = TS.TSEv} {I = ExtI TS.TSEv} as TSL
import Semantics.LTS {E = LNp.LNEv} {I = ExtI LNp.LNEv} as LNL
import Semantics.LTS {E = LFp.LFEv} {I = ExtI LFp.LFEv} as LFL
open import Data.Bool using ( Bool; true; false )
open import Data.Nat using ( ℕ; zero; suc )
open import Data.Fin using ( Fin ) renaming ( zero to fzero; suc to fsuc )
open import Data.List using ( map )
open import Class.DecEq using ( _≟_ )
-- the breakable medium decode (for the medium api-non-offer leaf)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( decMed; decLink; decCopy; MedState; mkMed; phase; broken; CopyPhase )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks; linkConfig; Block; decBlock )

-- Net_Api operators + the empty sync alphabet + the Par ev-elimination
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; EventSet; ⦀Fin; Skip; _△_; △-merge; Prefix₀ )
open EventSet using ( mem )
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
open Op using () renaming (∅ES to ∅ESa)
-- Net-level (pre-rename) operators: the copy fold `⦀⋆` for the medium leaf
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; τ; evl; evLabel; sVis; ev-inv; Event√; √ )
-- the Hide visible-event inversion (for the `oev` √/io impossible-event refutations)
open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
  using ( HideevR; Hide-ev-elim )
open HideevR using ( heV; he√ )

-- concrete node decodes + the generic bundle + the two drivers/phases
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA as SN
open SN
  using ( decNodeB; decNodeC; decNodeD; bundleG; decCP; decConsD
        ; consD; consuming; producing
        -- the two straight-chain drivers + their phase enumerations
        ; decProd; decCons; ProdPh; ConsPh
        ; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        -- the renamed-peer sources (for the concrete bundle break-non-offer)
        ; decCSc-src; decCSs-src; decBFc-src; decBFs-src )
-- the per-protocol process-type synonyms (the `{P′ : XProc}` sig fields of item 3a)
open SN
  using ( CSProc; BFProc; KAProc; TSProc; LNProc; LFProc )
-- the τ-free peer interpreter (`tableSpec`) + abstract positions/tables + the
-- inert KA/TS specs (for the ABSTRACT bundle break non-offer, `absBundleG` side)
import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs blkA as NS

-- the Net_Api prefix (`⟶₀`) visible-step inversion (for the role discriminator)
import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) as PInv
open PInv using ( ⟶₀-ev-inv )
-- abstract node decodes + the abstract bundle + the io-offer predicate
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA as SStep
open SStep
  using ( absNodeA; absNodeB; absNodeC; absNodeD; absBundleG; IoOffers )
-- the whole-system concrete decode + config record (for the top-level api peel)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
-- the shared io-hide alphabet (api events are disjoint from it)
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open SN using ( LFProc )
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

-- Data message constructors + payload wrappers used in the LF source-position clauses
open import CSP.Examples.Cardano_network.Data p using
  ( chainSync; keepAlive; blockFetch; txSubmission; leiosNotify; leiosFetch )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgKeepAlive; MsgKeepAliveResponse; MsgKADone )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgLNRequestNext; MsgLNBlockAnnouncement; MsgLNBlockOffer
  ; MsgLNBlockTxsOffer; MsgLNVotesOffer; MsgLNDone )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgLFBlockRequest; MsgLFBlock; MsgLFBlockTxsRequest; MsgLFBlockTxs
  ; MsgLFVotesRequest; MsgLFVoteDelivery; MsgLFBlockRangeRequest
  ; MsgLFNextBlockAndTxsInRange; MsgLFLastBlockAndTxsInRange; MsgLFDone )
open import CSP.Examples.Cardano_network.Net p using
  ( sendLFBlockRequest; sendLFBlockTxsRequest; sendLFVotesRequest
  ; sendLFBlockRangeRequest; sendLFDone; sendLFBlock; sendLFBlockTxs
  ; sendLFVoteDelivery; sendLFNextBlockAndTxsInRange; sendLFLastBlockAndTxsInRange
  ; recvLFBlock; recvLFBlockTxs; recvLFVoteDelivery; recvLFRangeBlock )
open import Data.List using ( List; []; _∷_ )
open import Data.List.Properties using ( ≡-dec )
import Class.DecEq.Instances as DecEqI
open import Class.DecEq using ( DecEq )
open Params p using ( time₀; length₀ )
open import CSP.Examples.Cardano_network.Base using ( FromResponder; FromInitiator )
-- BlockingStyle constructors: used in the TS `tcAri (Blocking/NonBlocking , …)`
-- position patterns; unimported they would be silent pattern variables and the
-- `tsCnxt` table would stay stuck on a non-constructor blocking flag
open import CSP.Examples.Cardano_network.Base using ( Blocking; NonBlocking )
-- the role tag TYPE + the `Messages` wire-message type (for `msgOrigin` below)
open import CSP.Examples.Cardano_network.Base using ( Mode )
open import CSP.Examples.Cardano_network.Data p using ( Messages )
-- CS / BF / TS wire-message constructors (for `msgOrigin`; KA/LN/LF already open)
open import CSP.Examples.Cardano_network.Data p using
  ( MsgCSRequestNext; MsgCSAwaitReply; MsgCSRollForward; MsgCSRollBackward
  ; MsgCSFindIntersect; MsgCSIntersectFound; MsgCSIntersectNotFound; MsgCSDone )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgRequestRange; MsgStartBatch; MsgNoBlocks; MsgBlock; MsgBatchDone; MsgClientDone )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgTSInit; MsgTSRequestTxIds; MsgTSReplyTxIds; MsgTSRequestTxs; MsgTSReplyTxs; MsgTSDone )

-- every SysOracle leaf lemma (re-exported so downstream sees them + the new LF pins)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA public


------------------------------------------------------------------------
-- ITEM-6 (io-peel) — LF channel bundle io-link pins (mirror of CS/BF/KA/TS/LN).
-- `decLFc/LFs-src-link` are byte-copies of the committed `-src-dir` blocks
-- (in SysOracle_RouteLnLf) returning `lfEvLink e₁ ≡ l`; `bundleLF-ev-link`
-- copies `bundle-LF-ev-inv`'s 12-peer peel, routing the two LF peers (the
-- INNERMOST ⦀ pair, LF end-asymmetry) to `lfc/lfs-ev-link` (link).
------------------------------------------------------------------------
-- the link component of a LF source event
lfEvLink : {X : Set 0ℓ} → LFp.LFEv X → Link
lfEvLink (LFp.sendLF l d)    = l
lfEvLink (LFp.receiveLF l d) = l
lfEvLink (LFp.apiLFev l d m) = l
lfEvLink (LFp.doneLF l d)    = l

-- ιLF carries the source link into the Net_Api event
lfApiLink : {X : Set 0ℓ} (e₁ : LFp.LFEv X) → ApiHasLink (lfEvLink e₁) (ιLF e₁)
lfApiLink (LFp.sendLF l d)    = ahlIn
lfApiLink (LFp.receiveLF l d) = ahlOut
lfApiLink (LFp.apiLFev l d m) = ahlLF
lfApiLink (LFp.doneLF l d)    = ahlDone

-- LINK: decLFc-src-link — a fine LF-client source step's event link is `l`
decLFc-src-link : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : LFProc}
  → decLFc-src l d pos LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e₁ a)) ]─► P′
  → lfEvLink e₁ ≡ l
-- head stIdle : five api requests
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFDone} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-link l d (lfcHead LFp.stIdle) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
-- head stBlock / stBlockTxs / stVotes / stBlockRange : wire receives
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlock b)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlock) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stVotes) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-link l d (lfcHead LFp.stBlockRange) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
-- head stDone : ret
decLFc-src-link l d (lfcHead LFp.stDone) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaves
decLFc-src-link l d (lfcRblk1 b) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d (lfcRblk1 b) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-src-link l d (lfcRblk1 b) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-src-link l d (lfcRblk1 b) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-src-link l d (lfcRbtx1 ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFBlockTxs) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val ts
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d (lfcRbtx1 ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-src-link l d (lfcRbtx1 ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-src-link l d (lfcRbtx1 ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-src-link l d (lfcRvot1 vs) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFVoteDelivery) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val vs
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d (lfcRvot1 vs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-src-link l d (lfcRvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-src-link l d (lfcRvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-src-link l d (lfcRnext1 b ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFRangeBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEqI.DecEq-× ⦄ val (b , ts)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d (lfcRnext1 b ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-src-link l d (lfcRnext1 b ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-src-link l d (lfcRnext1 b ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-src-link l d (lfcRlast1 b ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFRangeBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEqI.DecEq-× ⦄ val (b , ts)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d (lfcRlast1 b ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
decLFc-src-link l d (lfcRlast1 b ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
decLFc-src-link l d (lfcRlast1 b ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
-- send leaves
decLFc-src-link l d (lfcWblk1 pt) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d (lfcWblk1 pt) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-src-link l d (lfcWblk1 pt) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-src-link l d (lfcWblk1 pt) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-src-link l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-src-link l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-src-link l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-src-link l d (lfcWvot1 vs) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d (lfcWvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-src-link l d (lfcWvot1 vs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-src-link l d (lfcWvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-src-link l d (lfcWrng1 r) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d (lfcWrng1 r) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-src-link l d (lfcWrng1 r) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-src-link l d (lfcWrng1 r) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-src-link l d lfcDone1 {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-link l d lfcDone1 {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
decLFc-src-link l d lfcDone1 {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
decLFc-src-link l d lfcDone1 {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
-- loop re-entry
decLFc-src-link l d (lfcSil st) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decLFs-src-link — mirror for the LF-server positions
decLFs-src-link : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : LFProc}
  → decLFs-src l d pos LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e₁ a)) ]─► P′
  → lfEvLink e₁ ≡ l
-- head stIdle : five wire requests (4 loops + done)
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFDone)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-link l d (lfsHead LFp.stIdle) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
-- head stBlock / stBlockTxs / stVotes / stBlockRange : api sends
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlock} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlock) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stVotes) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-link l d (lfsHead LFp.stBlockRange) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
-- head stDone : ret
decLFs-src-link l d (lfsHead LFp.stDone) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf
decLFs-src-link l d lfsDone1 {e₁ = LFp.doneLF l' d'} {a} s with step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s
... | offer with LFp.LFEv-≟ (_ , LFp.doneLF l d) (_ , LFp.doneLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decLFs-src-link l d lfsDone1 {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
decLFs-src-link l d lfsDone1 {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
decLFs-src-link l d lfsDone1 {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
-- send leaves
decLFs-src-link l d (lfsWblk1 b) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-link l d (lfsWblk1 b) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-src-link l d (lfsWblk1 b) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-src-link l d (lfsWblk1 b) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-src-link l d (lfsWtxs1 ts) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-link l d (lfsWtxs1 ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-src-link l d (lfsWtxs1 ts) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-src-link l d (lfsWtxs1 ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-src-link l d (lfsWvot1 vs) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-link l d (lfsWvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-src-link l d (lfsWvot1 vs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-src-link l d (lfsWvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-src-link l d (lfsWnext1 (b , ts)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-link l d (lfsWnext1 (b , ts)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-src-link l d (lfsWnext1 (b , ts)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-src-link l d (lfsWnext1 (b , ts)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-src-link l d (lfsWlast1 (b , ts)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-link l d (lfsWlast1 (b , ts)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
decLFs-src-link l d (lfsWlast1 (b , ts)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
decLFs-src-link l d (lfsWlast1 (b , ts)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
-- loop re-entry
decLFs-src-link l d (lfsSil st) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- the link a driven LF-client step exposes on the Net_Api event
lfc-ev-link : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decLFc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
lfc-ev-link l d pos step with LFNO.renameMap-ev-reflect-ι {P = decLFc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιLF-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιLF e₁)) (decLFc-src-link l d pos srcStep) (lfApiLink e₁))

-- the link a driven LF-server step exposes on the Net_Api event
lfs-ev-link : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decLFs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
lfs-ev-link l d pos step with LFNO.renameMap-ev-reflect-ι {P = decLFs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιLF-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιLF e₁)) (decLFs-src-link l d pos srcStep) (lfApiLink e₁))

-- a bundleG LF-image step pins the bundle's link
bundleLF-ev-link : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► Bd′
  → ApiHasLink l (ιLF e₁)
bundleLF-ev-link l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...                     | PEA.evL _ sM = lfc-ev-link l cl (lfc ip) sM
...                     | PEA.evBoth _ sM sTail =
                          ⊥-elim (decLFs-dir-noOffer l sv (lfs ip) e₁
                            (λ q → cl≢sv (trans (apiDir-inj (lfc-ev-dir l cl (lfc ip) sM) (lfApiDir e₁)) q))
                            (_ , sTail))
...                     | PEA.evR _ qs = lfs-ev-link l sv (lfs ip) qs

-- a LF-channel `input` io step of a bundle pins the io's link to the bundle's
bundleLF-io-link-in : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (input l′ d′ N2N_LeiosFetch) a)) ]─► Bd′
  → l ≡ l′
bundleLF-io-link-in l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlIn-link (bundleLF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.sendLF l′ d′} step)

-- a LF-channel `output` io step of a bundle pins the io's link to the bundle's
bundleLF-io-link-out : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (output l′ d′ N2N_LeiosFetch) a)) ]─► Bd′
  → l ≡ l′
bundleLF-io-link-out l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlOut-link (bundleLF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.receiveLF l′ d′} step)

-- extra imports for the step-1.5 abstract idle-bundle link non-offers
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιKA; ιTS; ιLN )
open import CSP.Examples.Cardano_network.Net p using ( sendKAMsg; sendKADone; errCookie; recvKACookie )
-- TS/LN api-tag constructors used as patterns in the link-tables (else they
-- would be parsed as pattern variables shadowing the constructors → the table
-- stays stuck on a variable tag)
open import CSP.Examples.Cardano_network.Net p using
  ( sendTSReplyTxIds; sendTSReplyTxs; sendTSDone; sendTSRequestTxIdsBlocking
  ; sendTSRequestTxIdsPipelined; sendTSRequestTxsPipelined; recvTSRequestTxIds
  ; recvTSRequestTxs
  ; sendLNRequestNext; sendLNDone; sendLNBlockAnnouncement; sendLNBlockOffer
  ; sendLNBlockTxsOffer; sendLNVotesOffer; recvLNBlockAnnouncement
  ; recvLNBlockOffer; recvLNBlockTxsOffer; recvLNVotesOffer )
-- (TS message ctors are imported once above near `msgOrigin`; a second copy here
-- caused a term-position CantResolveOverloadedConstructors clash — removed.)
-- the per-peer abstract bundle decodes + their head-collapse coarsenings (SStep)
open SStep using
  ( absKAc; absKAs; absCSc; absCSs; absBFc; absBFs
  ; absTSc; absTSs; absLNc; absLNs; absLFc; absLFs
  ; coarsenKAc; coarsenKAs; coarsenTSc; coarsenTSs
  ; coarsenLNc; coarsenLNs; coarsenLFc; coarsenLFs )

------------------------------------------------------------------------
-- ITEM-6 groundwork (step 1.5) — abstract idle-bundle io-non-offers for the
-- KA/TS/LN/LF channels (the io-peel evBoth-refute enabler for nodeX-ev-io).
-- Layer 1: link-tables `xCnxt/Snxt-link-no` = validated dir->link mirror of the
--   committed `-dir-no` (only `yes refl | no _` flips to ⊥-elim ¬eq refl).
-- Layer 2: `absXc/Xs-link-noBoth` mirror `absCSc/CSs-link-noBoth`.
-- Layer 3: `absBundleG-X-link-noIoOffer` mirror `absBundleG-CS-link-noIoOffer`.
------------------------------------------------------------------------

-- ===== KA channel =====
-- LINK-TABLE: kaCnxt-link-no / kaSnxt-link-no (dir->link mirror)
kaCnxt-link-no : (l : Link) (d : Dir) (q : NS.KAcPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvLink e₁ ≢ l → NS.kaCnxt l d q (X , ιKA e₁) a ≡ nothing
-- kcClient : fires apiKA sendKAMsg / sendKADone
kaCnxt-link-no l d NS.kcClient (KA.apiKAev l' d' sendKAMsg) ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaCnxt-link-no l d NS.kcClient (KA.apiKAev l' d' sendKADone) ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaCnxt-link-no l d NS.kcClient (KA.apiKAev l' d' errCookie) ¬d = refl
kaCnxt-link-no l d NS.kcClient (KA.apiKAev l' d' recvKACookie) ¬d = refl
kaCnxt-link-no l d NS.kcClient (KA.sendKA l' d') ¬d = refl
kaCnxt-link-no l d NS.kcClient (KA.receiveKA l' d') ¬d = refl
kaCnxt-link-no l d NS.kcClient (KA.doneKA l' d') ¬d = refl
-- kcWmsg c : fires sendKA (input N2N_KeepAlive)
kaCnxt-link-no l d (NS.kcWmsg c) (KA.sendKA l' d') ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaCnxt-link-no l d (NS.kcWmsg c) (KA.receiveKA l' d') ¬d = refl
kaCnxt-link-no l d (NS.kcWmsg c) (KA.apiKAev l' d' m) ¬d = refl
kaCnxt-link-no l d (NS.kcWmsg c) (KA.doneKA l' d') ¬d = refl
-- kcWdone : fires sendKA (input N2N_KeepAlive)
kaCnxt-link-no l d NS.kcWdone (KA.sendKA l' d') ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaCnxt-link-no l d NS.kcWdone (KA.receiveKA l' d') ¬d = refl
kaCnxt-link-no l d NS.kcWdone (KA.apiKAev l' d' m) ¬d = refl
kaCnxt-link-no l d NS.kcWdone (KA.doneKA l' d') ¬d = refl
-- kcAwait c : fires receiveKA (output N2N_KeepAlive) with MsgKeepAliveResponse
kaCnxt-link-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAliveResponse c')} ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAlive _)} ¬d = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , keepAlive MsgKADone} ¬d = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , chainSync _} ¬d = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , blockFetch _} ¬d = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , txSubmission _} ¬d = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , leiosNotify _} ¬d = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , leiosFetch _} ¬d = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.sendKA l' d') ¬d = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.apiKAev l' d' m) ¬d = refl
kaCnxt-link-no l d (NS.kcAwait c) (KA.doneKA l' d') ¬d = refl
-- kcErr cq cr : fires apiKA errCookie
kaCnxt-link-no l d (NS.kcErr cq cr) (KA.apiKAev l' d' errCookie) ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaCnxt-link-no l d (NS.kcErr cq cr) (KA.apiKAev l' d' sendKAMsg) ¬d = refl
kaCnxt-link-no l d (NS.kcErr cq cr) (KA.apiKAev l' d' sendKADone) ¬d = refl
kaCnxt-link-no l d (NS.kcErr cq cr) (KA.apiKAev l' d' recvKACookie) ¬d = refl
kaCnxt-link-no l d (NS.kcErr cq cr) (KA.sendKA l' d') ¬d = refl
kaCnxt-link-no l d (NS.kcErr cq cr) (KA.receiveKA l' d') ¬d = refl
kaCnxt-link-no l d (NS.kcErr cq cr) (KA.doneKA l' d') ¬d = refl
-- kcTerm / kcTermE : terminal, no edges
kaCnxt-link-no l d NS.kcTerm  e₁ ¬d = refl
kaCnxt-link-no l d NS.kcTermE e₁ ¬d = refl

kaSnxt-link-no : (l : Link) (d : Dir) (q : NS.KAsPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvLink e₁ ≢ l → NS.kaSnxt l d q (X , ιKA e₁) a ≡ nothing
-- ksClient : fires receiveKA (output N2N_KeepAlive) with MsgKeepAlive / MsgKADone
kaSnxt-link-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAlive c)} ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaSnxt-link-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , keepAlive MsgKADone} ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaSnxt-link-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} ¬d = refl
kaSnxt-link-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , chainSync _} ¬d = refl
kaSnxt-link-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , blockFetch _} ¬d = refl
kaSnxt-link-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , txSubmission _} ¬d = refl
kaSnxt-link-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , leiosNotify _} ¬d = refl
kaSnxt-link-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , leiosFetch _} ¬d = refl
kaSnxt-link-no l d NS.ksClient (KA.sendKA l' d') ¬d = refl
kaSnxt-link-no l d NS.ksClient (KA.apiKAev l' d' m) ¬d = refl
kaSnxt-link-no l d NS.ksClient (KA.doneKA l' d') ¬d = refl
-- ksRecv c : fires apiKA recvKACookie
kaSnxt-link-no l d (NS.ksRecv c) (KA.apiKAev l' d' recvKACookie) ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaSnxt-link-no l d (NS.ksRecv c) (KA.apiKAev l' d' sendKAMsg) ¬d = refl
kaSnxt-link-no l d (NS.ksRecv c) (KA.apiKAev l' d' sendKADone) ¬d = refl
kaSnxt-link-no l d (NS.ksRecv c) (KA.apiKAev l' d' errCookie) ¬d = refl
kaSnxt-link-no l d (NS.ksRecv c) (KA.sendKA l' d') ¬d = refl
kaSnxt-link-no l d (NS.ksRecv c) (KA.receiveKA l' d') ¬d = refl
kaSnxt-link-no l d (NS.ksRecv c) (KA.doneKA l' d') ¬d = refl
-- ksResp c : fires sendKA (input N2N_KeepAlive) with MsgKeepAliveResponse
kaSnxt-link-no l d (NS.ksResp c) (KA.sendKA l' d') ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaSnxt-link-no l d (NS.ksResp c) (KA.receiveKA l' d') ¬d = refl
kaSnxt-link-no l d (NS.ksResp c) (KA.apiKAev l' d' m) ¬d = refl
kaSnxt-link-no l d (NS.ksResp c) (KA.doneKA l' d') ¬d = refl
-- ksDdone : fires doneKA (done N2N_KeepAlive)
kaSnxt-link-no l d NS.ksDdone (KA.doneKA l' d') ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
kaSnxt-link-no l d NS.ksDdone (KA.sendKA l' d') ¬d = refl
kaSnxt-link-no l d NS.ksDdone (KA.receiveKA l' d') ¬d = refl
kaSnxt-link-no l d NS.ksDdone (KA.apiKAev l' d' m) ¬d = refl
-- ksTerm : terminal, no edges
kaSnxt-link-no l d NS.ksTerm e₁ ¬d = refl

-- an idle same-protocol KA-client bundle at a DIFFERENT link does not fire
absKAc-link-noBoth : (l : Link) (sv : Dir) (q : KAcPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvLink e₁ ≢ l → ¬ IoOffers (absKAc l sv q) (ιKA e₁) a
absKAc-link-noBoth l sv q e₁ {a} ¬l with NS.kaCfin (coarsenKAc q) in fEq
... | true  = viewV→noOffer (absKAc l sv q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l sv })
                   (coarsenKAc q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAc l sv q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l sv })
                   (coarsenKAc q) {e = ιKA e₁} {a = a} fEq (kaCnxt-link-no l sv (coarsenKAc q) e₁ {a = a} ¬l))

-- an idle same-protocol KA-server bundle at a DIFFERENT link does not fire
absKAs-link-noBoth : (l : Link) (sv : Dir) (q : KAsPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvLink e₁ ≢ l → ¬ IoOffers (absKAs l sv q) (ιKA e₁) a
absKAs-link-noBoth l sv q e₁ {a} ¬l with NS.kaSfin (coarsenKAs q) in fEq
... | true  = viewV→noOffer (absKAs l sv q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l sv })
                   (coarsenKAs q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAs l sv q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l sv })
                   (coarsenKAs q) {e = ιKA e₁} {a = a} fEq (kaSnxt-link-no l sv (coarsenKAs q) e₁ {a = a} ¬l))

-- ===== TS channel =====
-- LINK-TABLE: tsCnxt-link-no / tsSnxt-link-no (dir->link mirror)
tsCnxt-link-no : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvLink e₁ ≢ l → NS.tsCnxt l d q (X , ιTS e₁) a ≡ nothing
tsCnxt-link-no l d NS.tcInit (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d NS.tcInit (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcInit (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-link-no l d NS.tcInit (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.sendTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-link-no l d NS.tcIdle (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.sendTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (Blocking , a , r)) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.sendTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcAri (NonBlocking , a , r)) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.sendTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcArt _) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-link-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSDone) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-link-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-link-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-link-no l d NS.tcBlk (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsCnxt-link-no l d NS.tcBlk (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-link-no l d NS.tcBlk (TS.sendTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcBlk (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcBlk (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.sendTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcNbl (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.sendTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcTxs (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcWri _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d (NS.tcWri _) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcWri _) (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-link-no l d (NS.tcWri _) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcWdone (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d NS.tcWdone (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcWdone (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-link-no l d NS.tcWdone (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcWrt _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsCnxt-link-no l d (NS.tcWrt _) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d (NS.tcWrt _) (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-link-no l d (NS.tcWrt _) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcTerm (TS.sendTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcTerm (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-link-no l d NS.tcTerm (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-link-no l d NS.tcTerm (TS.doneTS l′ d′) ¬d = refl

tsSnxt-link-no : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvLink e₁ ≢ l → NS.tsSnxt l d q (X , ιTS e₁) a ≡ nothing
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.sendTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-link-no l d NS.tsInit (TS.doneTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsSnxt-link-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsSnxt-link-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsSnxt-link-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d NS.tsIdle (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsSnxt-link-no l d NS.tsIdle (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsSnxt-link-no l d NS.tsIdle (TS.sendTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsIdle (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsIdle (TS.doneTS l′ d′) ¬d = refl
tsSnxt-link-no l d (NS.tsWib _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d (NS.tsWib _) (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-link-no l d (NS.tsWib _) (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-link-no l d (NS.tsWib _) (TS.doneTS l′ d′) ¬d = refl
tsSnxt-link-no l d (NS.tsWin _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d (NS.tsWin _) (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-link-no l d (NS.tsWin _) (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-link-no l d (NS.tsWin _) (TS.doneTS l′ d′) ¬d = refl
tsSnxt-link-no l d (NS.tsWrt _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d (NS.tsWrt _) (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-link-no l d (NS.tsWrt _) (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-link-no l d (NS.tsWrt _) (TS.doneTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.sendTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-link-no l d NS.tsBlk (TS.doneTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.sendTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-link-no l d NS.tsNbl (TS.doneTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.sendTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-link-no l d NS.tsTxs (TS.doneTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsDdone (TS.doneTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
tsSnxt-link-no l d NS.tsDdone (TS.sendTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsDdone (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsDdone (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-link-no l d NS.tsTerm (TS.sendTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsTerm (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-link-no l d NS.tsTerm (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-link-no l d NS.tsTerm (TS.doneTS l′ d′) ¬d = refl

-- an idle same-protocol TS-client bundle at a DIFFERENT link does not fire
absTSc-link-noBoth : (l : Link) (sv : Dir) (q : TScPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvLink e₁ ≢ l → ¬ IoOffers (absTSc l sv q) (ιTS e₁) a
absTSc-link-noBoth l sv q e₁ {a} ¬l with NS.tsCfin (coarsenTSc q) in fEq
... | true  = viewV→noOffer (absTSc l sv q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l sv })
                   (coarsenTSc q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSc l sv q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l sv })
                   (coarsenTSc q) {e = ιTS e₁} {a = a} fEq (tsCnxt-link-no l sv (coarsenTSc q) e₁ {a = a} ¬l))

-- an idle same-protocol TS-server bundle at a DIFFERENT link does not fire
absTSs-link-noBoth : (l : Link) (sv : Dir) (q : TSsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvLink e₁ ≢ l → ¬ IoOffers (absTSs l sv q) (ιTS e₁) a
absTSs-link-noBoth l sv q e₁ {a} ¬l with NS.tsSfin (coarsenTSs q) in fEq
... | true  = viewV→noOffer (absTSs l sv q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l sv })
                   (coarsenTSs q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSs l sv q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l sv })
                   (coarsenTSs q) {e = ιTS e₁} {a = a} fEq (tsSnxt-link-no l sv (coarsenTSs q) e₁ {a = a} ¬l))

-- ===== LN channel =====
-- LINK-TABLE: lnCnxt-link-no / lnSnxt-link-no (dir->link mirror)
lnCnxt-link-no : (l : Link) (d : Dir) (q : NS.LNcPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvLink e₁ ≢ l → NS.lnCnxt l d q (X , ιLN e₁) a ≡ nothing
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNDone) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncIdle (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncWreq (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d NS.lncWreq (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncWreq (LNp.apiLNev l′ d′ m) ¬d = refl
lnCnxt-link-no l d NS.lncWreq (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncWdone (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d NS.lncWdone (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncWdone (LNp.apiLNev l′ d′ m) ¬d = refl
lnCnxt-link-no l d NS.lncWdone (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify MsgLNRequestNext} ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify MsgLNDone} ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.apiLNev l′ d′ m) ¬d = refl
lnCnxt-link-no l d NS.lncBusy (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRann _) (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRoff _) (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRtxs _) (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-link-no l d (NS.lncRvot _) (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncTerm (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncTerm (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-link-no l d NS.lncTerm (LNp.apiLNev l′ d′ m) ¬d = refl
lnCnxt-link-no l d NS.lncTerm (LNp.doneLN l′ d′) ¬d = refl

lnSnxt-link-no : (l : Link) (d : Dir) (q : NS.LNsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvLink e₁ ≢ l → NS.lnSnxt l d q (X , ιLN e₁) a ≡ nothing
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify MsgLNRequestNext} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify MsgLNDone} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.sendLN l′ d′) ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-link-no l d NS.lnsIdle (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.sendLN l′ d′) ¬d = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-link-no l d NS.lnsBusy (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-link-no l d (NS.lnsWann _) (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d (NS.lnsWann _) (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-link-no l d (NS.lnsWann _) (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-link-no l d (NS.lnsWann _) (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-link-no l d (NS.lnsWoff _) (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d (NS.lnsWoff _) (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-link-no l d (NS.lnsWoff _) (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-link-no l d (NS.lnsWoff _) (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-link-no l d (NS.lnsWtxs _) (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d (NS.lnsWtxs _) (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-link-no l d (NS.lnsWtxs _) (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-link-no l d (NS.lnsWtxs _) (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-link-no l d (NS.lnsWvot _) (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d (NS.lnsWvot _) (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-link-no l d (NS.lnsWvot _) (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-link-no l d (NS.lnsWvot _) (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-link-no l d NS.lnsDone (LNp.doneLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lnSnxt-link-no l d NS.lnsDone (LNp.sendLN l′ d′) ¬d = refl
lnSnxt-link-no l d NS.lnsDone (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-link-no l d NS.lnsDone (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-link-no l d NS.lnsTerm (LNp.sendLN l′ d′) ¬d = refl
lnSnxt-link-no l d NS.lnsTerm (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-link-no l d NS.lnsTerm (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-link-no l d NS.lnsTerm (LNp.doneLN l′ d′) ¬d = refl

-- an idle same-protocol LN-client bundle at a DIFFERENT link does not fire
absLNc-link-noBoth : (l : Link) (sv : Dir) (q : LNcPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvLink e₁ ≢ l → ¬ IoOffers (absLNc l sv q) (ιLN e₁) a
absLNc-link-noBoth l sv q e₁ {a} ¬l with NS.lnCfin (coarsenLNc q) in fEq
... | true  = viewV→noOffer (absLNc l sv q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l sv })
                   (coarsenLNc q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNc l sv q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l sv })
                   (coarsenLNc q) {e = ιLN e₁} {a = a} fEq (lnCnxt-link-no l sv (coarsenLNc q) e₁ {a = a} ¬l))

-- an idle same-protocol LN-server bundle at a DIFFERENT link does not fire
absLNs-link-noBoth : (l : Link) (sv : Dir) (q : LNsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvLink e₁ ≢ l → ¬ IoOffers (absLNs l sv q) (ιLN e₁) a
absLNs-link-noBoth l sv q e₁ {a} ¬l with NS.lnSfin (coarsenLNs q) in fEq
... | true  = viewV→noOffer (absLNs l sv q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l sv })
                   (coarsenLNs q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNs l sv q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l sv })
                   (coarsenLNs q) {e = ιLN e₁} {a = a} fEq (lnSnxt-link-no l sv (coarsenLNs q) e₁ {a = a} ¬l))

-- ===== LF channel =====
-- LINK-TABLE: lfCnxt-link-no / lfSnxt-link-no (dir->link mirror)
lfCnxt-link-no : (l : Link) (d : Dir) (q : NS.LFcPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvLink e₁ ≢ l → NS.lfCnxt l d q (X , ιLF e₁) a ≡ nothing
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFDone) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcIdle (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcWblk _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d (NS.lfcWblk _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcWblk _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d (NS.lfcWblk _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcWtxs _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d (NS.lfcWtxs _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcWtxs _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d (NS.lfcWtxs _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcWvot _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d (NS.lfcWvot _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcWvot _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d (NS.lfcWvot _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcWrng _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d (NS.lfcWrng _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcWrng _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d (NS.lfcWrng _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcWdone (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcWdone (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcWdone (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d NS.lfcWdone (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d NS.lfcBlk (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d NS.lfcBtx (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d NS.lfcVot (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d NS.lfcRng (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRblk _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRbtx _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRvot _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRnextRng _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d (NS.lfcRlastRng _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcTerm (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcTerm (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-link-no l d NS.lfcTerm (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-link-no l d NS.lfcTerm (LFp.doneLF l′ d′) ¬d = refl

lfSnxt-link-no : (l : Link) (d : Dir) (q : NS.LFsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvLink e₁ ≢ l → NS.lfSnxt l d q (X , ιLF e₁) a ≡ nothing
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-link-no l d NS.lfsIdle (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlock) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsBlk (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsBtx (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsVot (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsRng (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWblk _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d (NS.lfsWblk _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWblk _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-link-no l d (NS.lfsWblk _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWtxs _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d (NS.lfsWtxs _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWtxs _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-link-no l d (NS.lfsWtxs _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWvot _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d (NS.lfsWvot _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWvot _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-link-no l d (NS.lfsWvot _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWnext _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d (NS.lfsWnext _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWnext _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-link-no l d (NS.lfsWnext _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWlast _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d (NS.lfsWlast _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d (NS.lfsWlast _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-link-no l d (NS.lfsWlast _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsDone (LFp.doneLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = ⊥-elim (¬d refl)
... | no _ | _ = refl
lfSnxt-link-no l d NS.lfsDone (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsDone (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsDone (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-link-no l d NS.lfsTerm (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsTerm (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-link-no l d NS.lfsTerm (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-link-no l d NS.lfsTerm (LFp.doneLF l′ d′) ¬d = refl

-- an idle same-protocol LF-client bundle at a DIFFERENT link does not fire
absLFc-link-noBoth : (l : Link) (sv : Dir) (q : LFcPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvLink e₁ ≢ l → ¬ IoOffers (absLFc l sv q) (ιLF e₁) a
absLFc-link-noBoth l sv q e₁ {a} ¬l with NS.lfCfin (coarsenLFc q) in fEq
... | true  = viewV→noOffer (absLFc l sv q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l sv })
                   (coarsenLFc q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFc l sv q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l sv })
                   (coarsenLFc q) {e = ιLF e₁} {a = a} fEq (lfCnxt-link-no l sv (coarsenLFc q) e₁ {a = a} ¬l))

-- an idle same-protocol LF-server bundle at a DIFFERENT link does not fire
absLFs-link-noBoth : (l : Link) (sv : Dir) (q : LFsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvLink e₁ ≢ l → ¬ IoOffers (absLFs l sv q) (ιLF e₁) a
absLFs-link-noBoth l sv q e₁ {a} ¬l with NS.lfSfin (coarsenLFs q) in fEq
... | true  = viewV→noOffer (absLFs l sv q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l sv })
                   (coarsenLFs q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFs l sv q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l sv })
                   (coarsenLFs q) {e = ιLF e₁} {a = a} fEq (lfSnxt-link-no l sv (coarsenLFs q) e₁ {a = a} ¬l))

-- absBundleG-KA-link-noIoOffer: idle KA-image ιKA e₁ at a DIFFERENT link
absBundleG-KA-link-noIoOffer : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvLink e₁ ≢ l → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) (ιKA e₁) a
absBundleG-KA-link-noIoOffer l cl sv qcc qcs qbc qbs ip e₁ ¬l =
  (SStep.⦀-noOffer (absKAc l cl (kac ip)) _ (absKAc-link-noBoth l cl (kac ip) e₁ ¬l)
   (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-link-noBoth l sv (kas ip) e₁ ¬l)
    (SStep.⦀-noOffer (absCSc l cl (qcc)) _ (absCSc-noKA l cl (qcc) e₁)
     (SStep.⦀-noOffer (absCSs l sv (qcs)) _ (absCSs-noKA l sv (qcs) e₁)
      (SStep.⦀-noOffer (absBFc l cl (qbc)) _ (absBFc-noKA l cl (qbc) e₁)
       (SStep.⦀-noOffer (absBFs l sv (qbs)) _ (absBFs-noKA l sv (qbs) e₁)
        (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noKA l cl (tsc ip) e₁)
         (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noKA l sv (tss ip) e₁)
          (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noKA l cl (lnc ip) e₁)
           (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noKA l sv (lns ip) e₁)
            (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
              (absLFc-noKA l cl (lfc ip) e₁) (absLFs-noKA l sv (lfs ip) e₁))))))))))))

-- absBundleG-TS-link-noIoOffer: idle TS-image ιTS e₁ at a DIFFERENT link
absBundleG-TS-link-noIoOffer : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvLink e₁ ≢ l → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) (ιTS e₁) a
absBundleG-TS-link-noIoOffer l cl sv qcc qcs qbc qbs ip e₁ ¬l =
  (SStep.⦀-noOffer (absKAc l cl (kac ip)) _ (absKAc-noTS l cl (kac ip) e₁)
   (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-noTS l sv (kas ip) e₁)
    (SStep.⦀-noOffer (absCSc l cl (qcc)) _ (absCSc-noTS l cl (qcc) e₁)
     (SStep.⦀-noOffer (absCSs l sv (qcs)) _ (absCSs-noTS l sv (qcs) e₁)
      (SStep.⦀-noOffer (absBFc l cl (qbc)) _ (absBFc-noTS l cl (qbc) e₁)
       (SStep.⦀-noOffer (absBFs l sv (qbs)) _ (absBFs-noTS l sv (qbs) e₁)
        (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-link-noBoth l cl (tsc ip) e₁ ¬l)
         (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-link-noBoth l sv (tss ip) e₁ ¬l)
          (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noTS l cl (lnc ip) e₁)
           (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noTS l sv (lns ip) e₁)
            (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
              (absLFc-noTS l cl (lfc ip) e₁) (absLFs-noTS l sv (lfs ip) e₁))))))))))))


-- absBundleG-LN-link-noIoOffer: idle LN-image ιLN e₁ at a DIFFERENT link
absBundleG-LN-link-noIoOffer : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvLink e₁ ≢ l → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) (ιLN e₁) a
absBundleG-LN-link-noIoOffer l cl sv qcc qcs qbc qbs ip e₁ ¬l =
  (SStep.⦀-noOffer (absKAc l cl (kac ip)) _ (absKAc-noLN l cl (kac ip) e₁)
   (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-noLN l sv (kas ip) e₁)
    (SStep.⦀-noOffer (absCSc l cl (qcc)) _ (absCSc-noLN l cl (qcc) e₁)
     (SStep.⦀-noOffer (absCSs l sv (qcs)) _ (absCSs-noLN l sv (qcs) e₁)
      (SStep.⦀-noOffer (absBFc l cl (qbc)) _ (absBFc-noLN l cl (qbc) e₁)
       (SStep.⦀-noOffer (absBFs l sv (qbs)) _ (absBFs-noLN l sv (qbs) e₁)
        (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noLN l cl (tsc ip) e₁)
         (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noLN l sv (tss ip) e₁)
          (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-link-noBoth l cl (lnc ip) e₁ ¬l)
           (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-link-noBoth l sv (lns ip) e₁ ¬l)
            (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
              (absLFc-noLN l cl (lfc ip) e₁) (absLFs-noLN l sv (lfs ip) e₁))))))))))))

-- absBundleG-LF-link-noIoOffer: idle LF-image ιLF e₁ at a DIFFERENT link
absBundleG-LF-link-noIoOffer : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvLink e₁ ≢ l → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) (ιLF e₁) a
absBundleG-LF-link-noIoOffer l cl sv qcc qcs qbc qbs ip e₁ ¬l =
  (SStep.⦀-noOffer (absKAc l cl (kac ip)) _ (absKAc-noLF l cl (kac ip) e₁)
   (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-noLF l sv (kas ip) e₁)
    (SStep.⦀-noOffer (absCSc l cl (qcc)) _ (absCSc-noLF l cl (qcc) e₁)
     (SStep.⦀-noOffer (absCSs l sv (qcs)) _ (absCSs-noLF l sv (qcs) e₁)
      (SStep.⦀-noOffer (absBFc l cl (qbc)) _ (absBFc-noLF l cl (qbc) e₁)
       (SStep.⦀-noOffer (absBFs l sv (qbs)) _ (absBFs-noLF l sv (qbs) e₁)
        (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noLF l cl (tsc ip) e₁)
         (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noLF l sv (tss ip) e₁)
          (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noLF l cl (lnc ip) e₁)
           (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noLF l sv (lns ip) e₁)
            (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
              (absLFc-link-noBoth l cl (lfc ip) e₁ ¬l) (absLFs-link-noBoth l sv (lfs ip) e₁ ¬l))))))))))))


------------------------------------------------------------------------
-- ITEM-2 (io-peel) — the per-node io SOLO inversions `nodeX-ev-io`.  A node is
-- `(bundleG l₁ ⦀ bundleG l₂) ∥⇘ apiES ⇙ driver`.  A delivered io `(e,a) ∈ ioES`
-- fires SOLO on ONE bundle: io ∉ apiES (`io⇒¬api`) rules out a driver↔bundle
-- sync (`evSync`), and the driver offers only api (`decProd/decCP/decConsD-io-no`)
-- so the top `∥⇘apiES⇙` peel lands on the bundle-`⦀` (`evL`).  The bundle-`⦀`
-- `evBoth` overlap (BOTH links firing the same io) is refuted by the io's OWN
-- link (`bundleG-io-ahl` pins it to each bundle's distinct link; `apiLink-inj`);
-- the firing bundle is inverted by the TOTAL `bundle-io-inv`.  The abstract node
-- redoes the SAME solo (`∥⇘⇙-ev-soloL`, driver idle via the driver io-no; idle
-- sibling bundle via `absBundleG-io-no` at the DIFFERENT link).
------------------------------------------------------------------------

-- an io event is not an api CS/BF/done event (IsApiCSBF is empty for input/output)
io⇒¬aicsbf : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → ¬ IsApiCSBF e
io⇒¬aicsbf {e = input  _ _ _} _ ()
io⇒¬aicsbf {e = output _ _ _} _ ()
io⇒¬aicsbf {e = sndmsg _ _ _} ()
io⇒¬aicsbf {e = rcvmsg _ _ _} ()
io⇒¬aicsbf {e = tx     _ _ _} ()
io⇒¬aicsbf {e = sndack _ _ _} ()
io⇒¬aicsbf {e = rcvack _ _ _} ()
io⇒¬aicsbf {e = ack    _ _ _} ()
io⇒¬aicsbf {e = done   _ _ _} ()
io⇒¬aicsbf {e = apiCS  _ _ _} ()
io⇒¬aicsbf {e = apiBF  _ _ _} ()
io⇒¬aicsbf {e = apiKA  _ _ _} ()
io⇒¬aicsbf {e = apiTS  _ _ _} ()
io⇒¬aicsbf {e = apiLN  _ _ _} ()
io⇒¬aicsbf {e = apiLF  _ _ _} ()
io⇒¬aicsbf {e = break  _}     ()

-- a bundle io step pins the io's OWN link to the bundle's link (`ApiHasLink l e`),
-- routing each io channel to its `bundleX-ev-link` (generic dispatcher over `e`)
bundleG-io-ahl : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → ApiHasLink l e
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_ChainSync}   iomem step = bundleCS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.sendCS    l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_ChainSync}   iomem step = bundleCS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.receiveCS l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_BlockFetch}  iomem step = bundleBF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.sendBF    l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_BlockFetch}  iomem step = bundleBF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.receiveBF l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_KeepAlive}   iomem step = bundleKA-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.sendKA    l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_KeepAlive}   iomem step = bundleKA-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.receiveKA l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_TxSubmission} iomem step = bundleTS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.sendTS    l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_TxSubmission} iomem step = bundleTS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.receiveTS l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosNotify} iomem step = bundleLN-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.sendLN   l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosNotify} iomem step = bundleLN-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.receiveLN l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosFetch}  iomem step = bundleLF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.sendLF   l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosFetch}  iomem step = bundleLF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.receiveLF l′ d′} step
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = done   _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiCS  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiBF  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiKA  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiTS  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiLN  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiLF  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} iomem step = ⊥-elim iomem
bundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     iomem step = ⊥-elim iomem

-- the whole idle abstract bundle at `l` offers nothing on an io `e` whose OWN
-- link `l₀` (witnessed by `ApiHasLink l₀ e`) is DIFFERENT (`l₀ ≢ l`) — generic
-- dispatcher over the io channel, routing to the per-channel `absBundleG-X-link-noIoOffer`
absBundleG-io-no : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {l₀ : Link}
  → ApiHasLink l₀ e → l₀ ≢ l → ioES .mem (X , e) a
  → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) e a
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = input  l′ d′ N2N_ChainSync}   ahlIn  l₀≢l iomem = absBundleG-CS-link-noIoOffer l cl sv qcc qcs qbc qbs ip (CS.sendCS    l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = output l′ d′ N2N_ChainSync}   ahlOut l₀≢l iomem = absBundleG-CS-link-noIoOffer l cl sv qcc qcs qbc qbs ip (CS.receiveCS l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = input  l′ d′ N2N_BlockFetch}  ahlIn  l₀≢l iomem = absBundleG-BF-link-noIoOffer l cl sv qcc qcs qbc qbs ip (BF.sendBF    l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = output l′ d′ N2N_BlockFetch}  ahlOut l₀≢l iomem = absBundleG-BF-link-noIoOffer l cl sv qcc qcs qbc qbs ip (BF.receiveBF l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = input  l′ d′ N2N_KeepAlive}   ahlIn  l₀≢l iomem = absBundleG-KA-link-noIoOffer l cl sv qcc qcs qbc qbs ip (KA.sendKA    l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = output l′ d′ N2N_KeepAlive}   ahlOut l₀≢l iomem = absBundleG-KA-link-noIoOffer l cl sv qcc qcs qbc qbs ip (KA.receiveKA l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = input  l′ d′ N2N_TxSubmission} ahlIn  l₀≢l iomem = absBundleG-TS-link-noIoOffer l cl sv qcc qcs qbc qbs ip (TS.sendTS    l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = output l′ d′ N2N_TxSubmission} ahlOut l₀≢l iomem = absBundleG-TS-link-noIoOffer l cl sv qcc qcs qbc qbs ip (TS.receiveTS l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = input  l′ d′ N2N_LeiosNotify} ahlIn  l₀≢l iomem = absBundleG-LN-link-noIoOffer l cl sv qcc qcs qbc qbs ip (LNp.sendLN   l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = output l′ d′ N2N_LeiosNotify} ahlOut l₀≢l iomem = absBundleG-LN-link-noIoOffer l cl sv qcc qcs qbc qbs ip (LNp.receiveLN l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = input  l′ d′ N2N_LeiosFetch}  ahlIn  l₀≢l iomem = absBundleG-LF-link-noIoOffer l cl sv qcc qcs qbc qbs ip (LFp.sendLF   l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = output l′ d′ N2N_LeiosFetch}  ahlOut l₀≢l iomem = absBundleG-LF-link-noIoOffer l cl sv qcc qcs qbc qbs ip (LFp.receiveLF l′ d′) l₀≢l
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = done   _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = apiCS  _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = apiBF  _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = apiKA  _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = apiTS  _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = apiLN  _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = apiLF  _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = sndmsg _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = rcvmsg _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = tx     _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = sndack _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = rcvack _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = ack    _ _ _} _ _ ()
absBundleG-io-no l cl sv qcc qcs qbc qbs ip {e = break  _}     _ _ ()

-- node-A driver-pair offers no io (both produce drivers are api-only)
nodeA-drv-io-no : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → ¬ IoOffers (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) e a
nodeA-drv-io-no na {X} {e} {a} iomem =
  SStep.⦀-noOffer _ _ (decProd-io-no linkAB hi blkA (SN.NodeStateA.prod-AB na) (io⇒¬aicsbf {X} {e} {a} iomem))
                      (decProd-io-no linkAC hi blkA (SN.NodeStateA.prod-AC na) (io⇒¬aicsbf {X} {e} {a} iomem))

-- firing link = linkAB: invert the AB bundle io, rebuild `na′`, lift abstract (⦀-ev-L)
nodeA-io-AB : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → SN.bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR na e a ((Bd′ ⦀ SN.bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AB na {X} {e} {a} iomem sBAB
  with bundle-io-inv linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB
... | bio csc′ css′ bfc′ bfs′ ip′ eq astep =
      naEv (SN.mkNodeA csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) ip′ (SN.NodeStateA.inert-AC na))
        (cong (λ z → (z ⦀ SN.bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (SStep.∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
                         (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
              astep
              (noOffer→viewV _ (absBundleG-io-no linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)
                 (bundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB) linkAB≢linkAC iomem)))
           (noOffer→viewV _ (nodeA-drv-io-no na iomem)))

-- firing link = linkAC (mirror via ⦀-ev-R)
nodeA-io-AC : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → SN.bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeAEvR na e a ((SN.bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ Bd′) ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-io-AC na {X} {e} {a} iomem sBAC
  with bundle-io-inv linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC
... | bio csc′ css′ bfc′ bfs′ ip′ eq astep =
      naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ css′ bfc′ bfs′ (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) ip′)
        (cong (λ z → (SN.bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ z) ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))) eq)
        (SStep.∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (SStep.⦀-ev-R (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
                         (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
              astep
              (noOffer→viewV _ (absBundleG-io-no linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
                 (bundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC) (λ q → linkAB≢linkAC (sym q)) iomem)))
           (noOffer→viewV _ (nodeA-drv-io-no na iomem)))

-- node-A io inversion: reflect the io as a bundle solo (driver idle), peel to the
-- firing link (`evBoth` refuted by distinct links), dispatch to `nodeA-io-AB/AC`
nodeA-ev-io : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → ioES .mem (X , e) a
  → SN.decNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → NodeAEvR na e a A′
nodeA-ev-io na {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (SN.bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ SN.bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeA-drv-io-no na iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeA-drv-io-no na iomem (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (SN.bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
          (apiLink-inj (bundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
                       (bundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)))
...   | PEA.evL _ sBAB = nodeA-io-AB na iomem sBAB
...   | PEA.evR _ sBAC = nodeA-io-AC na iomem sBAC


------------------------------------------------------------------------
-- ITEM-2 (io-peel) — node B/C/D io SOLO inversions (mirror `nodeA-ev-io`).
-- B/C are relay nodes (single `decCP` driver); D is a sink (two `decConsD`).
------------------------------------------------------------------------

-- distinct node links (Fin 4 literals) for the two-link `evBoth` refute
linkAB≢linkBD : ¬ (linkAB ≡ linkBD)
linkAB≢linkBD ()
linkAC≢linkCD : ¬ (linkAC ≡ linkCD)
linkAC≢linkCD ()
linkBD≢linkCD : ¬ (linkBD ≡ linkCD)
linkBD≢linkCD ()

-- node-B result: successor + concrete/abstract match (io analog of NodeBEvR)
data NodeBIoR (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (B′ : NetProc) : Set₁ where
  nbIo : (nb′ : SN.NodeStateB) → B′ ≡ SN.decNodeB nb′
       → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► absNodeB nb′
       → NodeBIoR nb e a B′

-- node-B driver (relay) offers no io
nodeB-drv-io-no : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → ¬ IoOffers (decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) e a
nodeB-drv-io-no nb {X} {e} {a} iomem = decCP-io-no linkAB linkBD (SN.NodeStateB.cp-B nb) (io⇒¬aicsbf {X} {e} {a} iomem)
-- firing link = linkAB
nodeB-io-AB : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBIoR nb e a ((Bd′ ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-AB nb {X} {e} {a} iomem sB
  with bundle-io-inv linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sB
... | bio csc′ css′ bfc′ bfs′ ip′ eq astep =
      nbIo (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) ip′ (SN.NodeStateB.inert-BD nb))
        (cong (λ z → (z ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (SStep.∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (SStep.⦀-ev-L (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
                         (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
              astep
              (noOffer→viewV _ (absBundleG-io-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)
                 (bundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sB) linkAB≢linkBD iomem)))
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem)))
-- firing link = linkBD
nodeB-io-BD : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeBIoR nb e a ((bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ Bd′) ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
nodeB-io-BD nb {X} {e} {a} iomem sB
  with bundle-io-inv linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sB
... | bio csc′ css′ bfc′ bfs′ ip′ eq astep =
      nbIo (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) ip′)
        (cong (λ z → (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) eq)
        (SStep.∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (SStep.⦀-ev-R (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
                         (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
              astep
              (noOffer→viewV _ (absBundleG-io-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                 (bundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sB) (λ q → linkAB≢linkBD (sym q)) iomem)))
           (noOffer→viewV _ (nodeB-drv-io-no nb iomem)))
-- node-B io inversion: bundle solo, peel to firing link, dispatch
nodeB-ev-io : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B′ : NetProc}
  → ioES .mem (X , e) a
  → SN.decNodeB nb ─[ ev (evl (evLabel X e a)) ]─► B′
  → NodeBIoR nb e a B′
nodeB-ev-io nb {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeB-drv-io-no nb iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeB-drv-io-no nb iomem (_ , sD))
... | PEA.evL _ sBb
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
           sBb
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
          (apiLink-inj (bundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
                       (bundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)))
...   | PEA.evL _ sBAB = nodeB-io-AB nb iomem sBAB
...   | PEA.evR _ sBBD = nodeB-io-BD nb iomem sBBD

-- node-C result + driver-no + solo inversions (relay: consume AC, produce CD)
data NodeCIoR (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (C′ : NetProc) : Set₁ where
  ncIo : (nc′ : SN.NodeStateC) → C′ ≡ SN.decNodeC nc′
       → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► absNodeC nc′
       → NodeCIoR nc e a C′

nodeC-drv-io-no : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → ¬ IoOffers (decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) e a
nodeC-drv-io-no nc {X} {e} {a} iomem = decCP-io-no linkAC linkCD (SN.NodeStateC.cp-C nc) (io⇒¬aicsbf {X} {e} {a} iomem)

-- firing link = linkAC
nodeC-io-AC : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCIoR nc e a ((Bd′ ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-AC nc {X} {e} {a} iomem sC
  with bundle-io-inv linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sC
... | bio csc′ css′ bfc′ bfs′ ip′ eq astep =
      ncIo (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) ip′ (SN.NodeStateC.inert-CD nc))
        (cong (λ z → (z ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (SStep.∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (SStep.⦀-ev-L (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
                         (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
              astep
              (noOffer→viewV _ (absBundleG-io-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)
                 (bundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sC) linkAC≢linkCD iomem)))
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem)))

-- firing link = linkCD
nodeC-io-CD : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeCIoR nc e a ((bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ Bd′) ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
nodeC-io-CD nc {X} {e} {a} iomem sC
  with bundle-io-inv linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sC
... | bio csc′ css′ bfc′ bfs′ ip′ eq astep =
      ncIo (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) ip′)
        (cong (λ z → (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) eq)
        (SStep.∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (SStep.⦀-ev-R (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
                         (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
              astep
              (noOffer→viewV _ (absBundleG-io-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                 (bundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sC) (λ q → linkAC≢linkCD (sym q)) iomem)))
           (noOffer→viewV _ (nodeC-drv-io-no nc iomem)))

nodeC-ev-io : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {C′ : NetProc}
  → ioES .mem (X , e) a
  → SN.decNodeC nc ─[ ev (evl (evLabel X e a)) ]─► C′
  → NodeCIoR nc e a C′
nodeC-ev-io nc {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeC-drv-io-no nc iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeC-drv-io-no nc iomem (_ , sD))
... | PEA.evL _ sCc
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
           sCc
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sCAC sCCD = ⊥-elim (linkAC≢linkCD
          (apiLink-inj (bundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sCAC)
                       (bundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sCCD)))
...   | PEA.evL _ sCAC = nodeC-io-AC nc iomem sCAC
...   | PEA.evR _ sCCD = nodeC-io-CD nc iomem sCCD

-- node-D result + driver-no + solo inversions (sink: two consume drivers)
data NodeDIoR (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (D′ : NetProc) : Set₁ where
  ndIo : (nd′ : SN.NodeStateD) → D′ ≡ SN.decNodeD nd′
       → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► absNodeD nd′
       → NodeDIoR nd e a D′

nodeD-drv-io-no : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → ¬ IoOffers (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)) e a
nodeD-drv-io-no nd {X} {e} {a} iomem =
  SStep.⦀-noOffer _ _ (decConsD-io-no linkBD (SN.NodeStateD.cons-BD nd) (io⇒¬aicsbf {X} {e} {a} iomem))
                      (decConsD-io-no linkCD (SN.NodeStateD.cons-CD nd) (io⇒¬aicsbf {X} {e} {a} iomem))

-- firing link = linkBD
nodeD-io-BD : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDIoR nd e a ((Bd′ ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-BD nd {X} {e} {a} iomem sD
  with bundle-io-inv linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sD
... | bio csc′ css′ bfc′ bfs′ ip′ eq astep =
      ndIo (SN.mkNodeD csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-BD nd) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
        (cong (λ z → (z ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)) eq)
        (SStep.∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (SStep.⦀-ev-L (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
                         (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
              astep
              (noOffer→viewV _ (absBundleG-io-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (bundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sD) linkBD≢linkCD iomem)))
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem)))

-- firing link = linkCD
nodeD-io-CD : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → NodeDIoR nd e a ((bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ Bd′) ∥⇘ apiES ⇙ (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-io-CD nd {X} {e} {a} iomem sD
  with bundle-io-inv linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sD
... | bio csc′ css′ bfc′ bfs′ ip′ eq astep =
      ndIo (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) ip′)
        (cong (λ z → (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)) eq)
        (SStep.∥⇘⇙-ev-soloL apiES _ _ (io⇒¬api {X} {e} {a} iomem)
           (SStep.⦀-ev-R (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
                         (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
              astep
              (noOffer→viewV _ (absBundleG-io-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (bundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sD) (λ q → linkBD≢linkCD (sym q)) iomem)))
           (noOffer→viewV _ (nodeD-drv-io-no nd iomem)))

nodeD-ev-io : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {D′ : NetProc}
  → ioES .mem (X , e) a
  → SN.decNodeD nd ─[ ev (evl (evLabel X e a)) ]─► D′
  → NodeDIoR nd e a D′
nodeD-ev-io nd {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sDr      = ⊥-elim (nodeD-drv-io-no nd iomem (_ , sDr))
... | PEA.evBoth _ _ sDr = ⊥-elim (nodeD-drv-io-no nd iomem (_ , sDr))
... | PEA.evL _ sDd
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
           sDd
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sDBD sDCD = ⊥-elim (linkBD≢linkCD
          (apiLink-inj (bundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sDBD)
                       (bundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sDCD)))
...   | PEA.evL _ sDBD = nodeD-io-BD nd iomem sDBD
...   | PEA.evR _ sDCD = nodeD-io-CD nd iomem sDCD


------------------------------------------------------------------------
-- ITEM-3 (io node disjointness) — the VALUE-ROLE discriminator CORE.
--
-- Route (a) make-or-break: at a FIXED nodes-level io label
-- `(input/output l d proto , a)`, two adjacent nodes share the link `(l,d)`
-- but hold OPPOSITE protocol roles (swapped `cl`/`sv`).  Link + dir + polarity
-- alone do NOT disambiguate them (node A's SERVER on `(linkAB,hi)` and node B's
-- CLIENT on `(linkAB,hi)` both fire `input linkAB hi`).  The VALUE `a` pins the
-- unique node: a client `!`-send / accept and a server `!`-send / accept
-- constrain the wire message's ORIGIN endpoint oppositely.
--
-- REFINEMENT vs `evboth-analysis.md` (source-verified below): the raw `Mode`
-- FIELD of `a` pins the role only for `input` (a `!`-send fixes it); on `output`
-- (a delivery) the receiving peer's offer map WILDCARDS the `Mode` field
-- (ChainSync.agda:207 `(_ , _ , _ , chainSync (MsgCSRollForward …))`), so at
-- nodes-level (pre-medium, `nodesOf s`) the `Mode` field is unconstrained on a
-- receive.  The invariant discriminator is instead the MESSAGE CONSTRUCTOR's
-- origin `msgOrigin` (which endpoint SENT it) — a client sends requests and
-- receives replies, a server the reverse.  `msgOrigin` is read off the message
-- constructor (verified against every `! (… , FromInitiator/FromResponder , …)`
-- send in ChainSync/BlockFetch/KeepAlive/TxSubmission/LeiosNotify/LeiosFetch).
--
-- NB TxSubmission is INVERTED from the request/reply naming: its SERVER
-- (responder) sends `MsgTSRequestTxIds/MsgTSRequestTxs` and its CLIENT
-- (initiator) replies `MsgTSReplyTxIds/MsgTSReplyTxs`, so those `Reply` ctors
-- are `FromInitiator` and `Request` ctors `FromResponder`.  Classified by the
-- ACTUAL `!`-send Mode, not the name.
------------------------------------------------------------------------

-- the ORIGINATING endpoint of a wire message: `FromInitiator` iff a client
-- `!`-sends it, `FromResponder` iff a server does (verbatim from the source
-- `! (… , FromInitiator/FromResponder , …)` sends of all six protocols)
msgOrigin : Messages → Mode
msgOrigin (keepAlive (MsgKeepAlive _))               = FromInitiator
msgOrigin (keepAlive (MsgKeepAliveResponse _))       = FromResponder
msgOrigin (keepAlive MsgKADone)                      = FromInitiator
msgOrigin (blockFetch (MsgRequestRange _))           = FromInitiator
msgOrigin (blockFetch MsgStartBatch)                 = FromResponder
msgOrigin (blockFetch MsgNoBlocks)                   = FromResponder
msgOrigin (blockFetch (MsgBlock _))                  = FromResponder
msgOrigin (blockFetch MsgBatchDone)                  = FromResponder
msgOrigin (blockFetch MsgClientDone)                 = FromInitiator
msgOrigin (chainSync MsgCSRequestNext)               = FromInitiator
msgOrigin (chainSync MsgCSAwaitReply)                = FromResponder
msgOrigin (chainSync (MsgCSRollForward _ _))         = FromResponder
msgOrigin (chainSync (MsgCSRollBackward _ _))        = FromResponder
msgOrigin (chainSync (MsgCSFindIntersect _))         = FromInitiator
msgOrigin (chainSync (MsgCSIntersectFound _ _))      = FromResponder
msgOrigin (chainSync (MsgCSIntersectNotFound _))     = FromResponder
msgOrigin (chainSync MsgCSDone)                      = FromInitiator
msgOrigin (txSubmission MsgTSInit)                   = FromInitiator
msgOrigin (txSubmission (MsgTSRequestTxIds _ _ _))   = FromResponder
msgOrigin (txSubmission (MsgTSReplyTxIds _))         = FromInitiator
msgOrigin (txSubmission (MsgTSRequestTxs _))         = FromResponder
msgOrigin (txSubmission (MsgTSReplyTxs _))           = FromInitiator
msgOrigin (txSubmission MsgTSDone)                   = FromInitiator
msgOrigin (leiosNotify MsgLNRequestNext)             = FromInitiator
msgOrigin (leiosNotify (MsgLNBlockAnnouncement _))   = FromResponder
msgOrigin (leiosNotify (MsgLNBlockOffer _))          = FromResponder
msgOrigin (leiosNotify (MsgLNBlockTxsOffer _))       = FromResponder
msgOrigin (leiosNotify (MsgLNVotesOffer _))          = FromResponder
msgOrigin (leiosNotify MsgLNDone)                    = FromInitiator
msgOrigin (leiosFetch (MsgLFBlockRequest _))         = FromInitiator
msgOrigin (leiosFetch (MsgLFBlock _))                = FromResponder
msgOrigin (leiosFetch (MsgLFBlockTxsRequest _ _))    = FromInitiator
msgOrigin (leiosFetch (MsgLFBlockTxs _))             = FromResponder
msgOrigin (leiosFetch (MsgLFVotesRequest _))         = FromInitiator
msgOrigin (leiosFetch (MsgLFVoteDelivery _))         = FromResponder
msgOrigin (leiosFetch (MsgLFBlockRangeRequest _))    = FromInitiator
msgOrigin (leiosFetch (MsgLFNextBlockAndTxsInRange _ _)) = FromResponder
msgOrigin (leiosFetch (MsgLFLastBlockAndTxsInRange _ _)) = FromResponder
msgOrigin (leiosFetch MsgLFDone)                     = FromInitiator

-- CLIENT value-role: a CLIENT peer offering io `(e,a)` constrains the value.
-- On a send (`input`) the wire message it emits is client-originated
-- (`msgOrigin ≡ FromInitiator`); on a delivery (`output`) it accepts only
-- server-originated messages (`msgOrigin ≡ FromResponder`).  Non-io events get
-- `⊤` (the client also fires api events — those clauses of a per-peer role
-- lemma discharge trivially, avoiding the api-event contamination of a global
-- result rewrite; io usage always supplies an `ioES` witness).
ClientIo : {X : Set 0ℓ} → Net_Api Payload X → X → Set
ClientIo (input  _ _ _) (_ , _ , _ , msg) = msgOrigin msg ≡ FromInitiator
ClientIo (output _ _ _) (_ , _ , _ , msg) = msgOrigin msg ≡ FromResponder
ClientIo _ _ = ⊤

-- SERVER value-role: the mirror (a server send is server-originated; a server
-- delivery accepts only client-originated messages)
ServerIo : {X : Set 0ℓ} → Net_Api Payload X → X → Set
ServerIo (input  _ _ _) (_ , _ , _ , msg) = msgOrigin msg ≡ FromResponder
ServerIo (output _ _ _) (_ , _ , _ , msg) = msgOrigin msg ≡ FromInitiator
ServerIo _ _ = ⊤

-- the two role tags are distinct
FI≢FR : FromInitiator ≢ FromResponder
FI≢FR ()

-- ROLE EXCLUSIVITY (the make-or-break refutation core): on a FIXED io event no
-- value can satisfy BOTH the client- and server-role constraints — so on a
-- shared `(l,d)` the two adjacent nodes (opposite roles) cannot both offer the
-- SAME `(e,a)`.  This is what item-3's pairwise `nodeY-io-no-when-X` /
-- `absNodeX-io-no-when-Y` will consume once the per-peer role fingerprints
-- (`decXc/Xs-io-role`) and the bundle assembly (`bundleG-io-role`) are built.
client-server-excl : {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
  → ioES .mem (X , e) a → ClientIo e a → ServerIo e a → ⊥
client-server-excl (input  _ _ _) (_ , _ , _ , msg) iomem ci si = FI≢FR (trans (sym ci) si)
client-server-excl (output _ _ _) (_ , _ , _ , msg) iomem ci si = FI≢FR (trans (sym si) ci)
client-server-excl (done  _ _ _) a () ci si
client-server-excl (apiCS _ _ _) a () ci si
client-server-excl (apiBF _ _ _) a () ci si
client-server-excl (apiKA _ _ _) a () ci si
client-server-excl (apiTS _ _ _) a () ci si
client-server-excl (apiLN _ _ _) a () ci si
client-server-excl (apiLF _ _ _) a () ci si
client-server-excl (sndmsg _ _ _) a () ci si
client-server-excl (rcvmsg _ _ _) a () ci si
client-server-excl (tx     _ _ _) a () ci si
client-server-excl (sndack _ _ _) a () ci si
client-server-excl (rcvack _ _ _) a () ci si
client-server-excl (ack    _ _ _) a () ci si
client-server-excl (break  _)     a () ci si

------------------------------------------------------------------------
-- ITEM 3a — per-peer io-role fingerprints (12 fns).  Mechanical transform
-- of the committed `decXc/Xs-src-dir`: same case analysis over the fine
-- position, but the visible-firing clause now proves `Client/ServerIo (ιX
-- e₁) a` (value's msgOrigin matches the peer role); io firings → refl,
-- api/done firings → tt (⊤).  TxSubmission role-inversion is in msgOrigin.
------------------------------------------------------------------------

-- io-role transform of decCSc-src-dir (item 3a): the fired event's value
-- carries the peer's client role (msgOrigin); non-io firings give ⊤.
decCSc-io-role : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSc-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → ClientIo (ιCS e₁) a
-- head stIdle : fires apiCSev sendCSRequestNext / FindIntersect / Done
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRequestNext} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} {a} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSDone} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollForward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollBackward}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollforward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollback}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-io-role l d (csHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
-- head stCanAwait : fires receiveCS RollForward / RollBackward / AwaitReply
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSAwaitReply} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-io-role l d (csHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
-- head stMustReply : fires receiveCS RollForward / RollBackward
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-io-role l d (csHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
-- head stIntersect : fires receiveCS IntersectFound / IntersectNotFound
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-io-role l d (csHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSc-io-role l d (csHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid csReqNext1 : fires sendCS payload → csSil stCanAwait
decCSc-io-role l d csReqNext1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-io-role l d csReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-io-role l d csReqNext1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-io-role l d csReqNext1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
-- mid csFindInt1 ps : fires sendCS payload → csSil stIntersect
decCSc-io-role l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-io-role l d (csFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-io-role l d (csFindInt1 ps) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-io-role l d (csFindInt1 ps) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
-- mid csDone1 : fires sendCS payload → csSil stDone (client has no node-local done)
decCSc-io-role l d csDone1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-io-role l d csDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-io-role l d csDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-io-role l d csDone1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
-- mid csRF1 : fires apiCSev recvCSRollforward (h,t) → csSil stIdle
decCSc-io-role l d (csRF1 h t) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollforward) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (h , t)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decCSc-io-role l d (csRF1 h t) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-io-role l d (csRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-io-role l d (csRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
-- mid csRB1 : fires apiCSev recvCSRollback (pt,tp) → csSil stIdle
decCSc-io-role l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollback) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decCSc-io-role l d (csRB1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-io-role l d (csRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-io-role l d (csRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
-- mid csIF1 : fires apiCSev recvCSIntersectFound (pt,tp) → csSil stIdle
decCSc-io-role l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decCSc-io-role l d (csIF1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-io-role l d (csIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-io-role l d (csIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
-- mid csINF1 : fires apiCSev recvCSIntersectNotFound tp → csSil stIdle
decCSc-io-role l d (csINF1 tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectNotFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ tp
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decCSc-io-role l d (csINF1 tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-io-role l d (csINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-io-role l d (csINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
-- loop re-entry csSil : forces to `sil`, no visible step
decCSc-io-role l d (csSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decCSs-src-dir (item 3a): the fired event's value
-- carries the peer's server role (msgOrigin); non-io firings give ⊤.
decCSs-io-role : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSs-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → ServerIo (ιCS e₁) a
-- head stIdle : receives RequestNext / FindIntersect / Done on the wire
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSRequestNext} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSFindIntersect ps)} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSDone} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-io-role l d (ssHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
-- head stCanAwait : sends RollForward / RollBackward / AwaitReply via api
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-io-role l d (ssHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
-- head stMustReply : sends RollForward / RollBackward via api
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-io-role l d (ssHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
-- head stIntersect : sends IntersectFound / IntersectNotFound via api
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollForward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollBackward}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollforward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollback}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSRequestNext}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-io-role l d (ssHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSs-io-role l d (ssHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid ssReqNext1 : fires api reqCSRequestNext (Prefix₀) → ssSil stCanAwait
decCSs-io-role l d ssReqNext1 {e₁ = CS.apiCSev l' d' m} s with step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSRequestNext) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = tt
decCSs-io-role l d ssReqNext1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-io-role l d ssReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-io-role l d ssReqNext1 {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
-- mid ssFindInt1 ps : fires api reqCSFindIntersect ps (Output) → ssSil stIntersect
decCSs-io-role l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSFindIntersect) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ CS.DecEq-ListPoint ⦄ a ps
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decCSs-io-role l d (ssFindInt1 ps) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-io-role l d (ssFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-io-role l d (ssFindInt1 ps) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
-- mid ssDone1 : fires doneCS (Prefix₀) → ssSil stDone
decCSs-io-role l d ssDone1 {e₁ = CS.doneCS l' d'} s with step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.doneCS l d) (_ , CS.doneCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = tt
decCSs-io-role l d ssDone1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-io-role l d ssDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-io-role l d ssDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
-- mid ssRF1 : fires sendCS payload → ssSil stIdle
decCSs-io-role l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-io-role l d (ssRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-io-role l d (ssRF1 h t) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-io-role l d (ssRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
-- mid ssRB1 : fires sendCS payload → ssSil stIdle
decCSs-io-role l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-io-role l d (ssRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-io-role l d (ssRB1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-io-role l d (ssRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
-- mid ssAw1 : fires sendCS payload → ssSil stMustReply
decCSs-io-role l d ssAw1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-io-role l d ssAw1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-io-role l d ssAw1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-io-role l d ssAw1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
-- mid ssIF1 : fires sendCS payload → ssSil stIdle
decCSs-io-role l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-io-role l d (ssIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-io-role l d (ssIF1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-io-role l d (ssIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
-- mid ssINF1 : fires sendCS payload → ssSil stIdle
decCSs-io-role l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-io-role l d (ssINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-io-role l d (ssINF1 tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-io-role l d (ssINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
-- loop re-entry ssSil : forces to `sil`, no visible step
decCSs-io-role l d (ssSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decBFc-src-dir (item 3a): the fired event's value
-- carries the peer's client role (msgOrigin); non-io firings give ⊤.
decBFc-io-role : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFc-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → ClientIo (ιBF e₁) a
-- head stIdle : sends RequestRange / ClientDone via api
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFRequestRange} {a} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFClientDone} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' recvBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' reqBFRange}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-io-role l d (bcHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
-- head stBusy : receives StartBatch / NoBlocks (both go straight to a re-entry sil)
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgStartBatch} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgNoBlocks} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-io-role l d (bcHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
-- head stStreaming : receives Block (→ bcBlk1) / BatchDone (→ re-entry sil)
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgBlock b)} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgBatchDone} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-io-role l d (bcHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
-- head stDone : `ret`, no visible step
decBFc-io-role l d (bcHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bcReq1 r : fires sendBF payload → bcSil stBusy
decBFc-io-role l d (bcReq1 r) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-io-role l d (bcReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-io-role l d (bcReq1 r) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-io-role l d (bcReq1 r) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
-- mid bcDone1 : fires sendBF payload → bcSil stDone
decBFc-io-role l d bcDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-io-role l d bcDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-io-role l d bcDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-io-role l d bcDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
-- mid bcBlk1 b : fires apiBFev recvBFBlock b → bcSil stStreaming
decBFc-io-role l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d recvBFBlock) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decBFc-io-role l d (bcBlk1 b) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-io-role l d (bcBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-io-role l d (bcBlk1 b) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
-- loop re-entry bcSil : forces to `sil`, no visible step
decBFc-io-role l d (bcSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decBFs-src-dir (item 3a): the fired event's value
-- carries the peer's server role (msgOrigin); non-io firings give ⊤.
decBFs-io-role : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFs-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → ServerIo (ιBF e₁) a
-- head stIdle : receives RequestRange (→ bsReq1) / ClientDone (→ bsDone1)
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgClientDone} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-io-role l d (bsHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
-- head stBusy : sends StartBatch (→ bsStart1) / NoBlocks (→ bsNoBlk1) via api
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFNoBlocks} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBatchDone}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-io-role l d (bsHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
-- head stStreaming : sends Block (→ bsBlk1) / BatchDone (→ bsBatchDone1) via api
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBlock} {a} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBatchDone} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFStartBatch}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}     s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-io-role l d (bsHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
-- head stDone : `ret`
decBFs-io-role l d (bsHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bsReq1 r : fires api reqBFRange r (Output) → bsSil stBusy
decBFs-io-role l d (bsReq1 r) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d reqBFRange) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEq-ChainRange ⦄ a r
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decBFs-io-role l d (bsReq1 r) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-io-role l d (bsReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-io-role l d (bsReq1 r) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
-- mid bsDone1 : fires doneBF (Prefix₀) → bsSil stDone
decBFs-io-role l d bsDone1 {e₁ = BF.doneBF l' d'} s with step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.doneBF l d) (_ , BF.doneBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = tt
decBFs-io-role l d bsDone1 {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-io-role l d bsDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-io-role l d bsDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
-- mid bsStart1 : fires sendBF payload → bsSil stStreaming
decBFs-io-role l d bsStart1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-io-role l d bsStart1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-io-role l d bsStart1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-io-role l d bsStart1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
-- mid bsNoBlk1 : fires sendBF payload → bsSil stIdle
decBFs-io-role l d bsNoBlk1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-io-role l d bsNoBlk1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-io-role l d bsNoBlk1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-io-role l d bsNoBlk1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
-- mid bsBlk1 b : fires sendBF payload → bsSil stStreaming
decBFs-io-role l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-io-role l d (bsBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-io-role l d (bsBlk1 b) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-io-role l d (bsBlk1 b) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
-- mid bsBatchDone1 : fires sendBF payload → bsSil stIdle
decBFs-io-role l d bsBatchDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-io-role l d bsBatchDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-io-role l d bsBatchDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-io-role l d bsBatchDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
-- loop re-entry bsSil : forces to `sil`, no visible step
decBFs-io-role l d (bsSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decKAc-src-dir (item 3a): the fired event's value
-- carries the peer's client role (msgOrigin); non-io firings give ⊤.
decKAc-io-role : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : KAProc}
  → decKAc-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e₁ a)) ]─► P′
  → ClientIo (ιKA e₁) a
decKAc-io-role l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' sendKAMsg} {a} s with step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decKAc-io-role l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' sendKADone} {a} s with step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tt
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decKAc-io-role l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' errCookie}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-io-role l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' recvKACookie} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-io-role l d (kcHead KA.stClient) {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-io-role l d (kcHead KA.stClient) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-io-role l d (kcHead KA.stClient) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAliveResponse cr)} s with step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAlive c)} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive MsgKADone}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.sendKA l' d'}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.apiKAev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead (KA.stServer cq)) {e₁ = KA.doneKA l' d'}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-io-role l d (kcHead KA.stDone) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAc-io-role l d (kcErr1 cq cr ne) s = ⊥-elim (ne refl)
decKAc-io-role l d (kcReq1 c) {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decKAc-io-role l d (kcReq1 c) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-io-role l d (kcReq1 c) {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-io-role l d (kcReq1 c) {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-io-role l d kcDone1 {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decKAc-io-role l d kcDone1 {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-io-role l d kcDone1 {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-io-role l d kcDone1 {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-io-role l d (kcSil st) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAc-io-role l d kcTermE1 s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decKAs-src-dir (item 3a): the fired event's value
-- carries the peer's server role (msgOrigin); non-io firings give ⊤.
decKAs-io-role : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : KAProc}
  → decKAs-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e₁ a)) ]─► P′
  → ServerIo (ιKA e₁) a
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAlive c)} s with step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive MsgKADone} s with step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAliveResponse c)} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.sendKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-io-role l d (ksHead KA.stClient) {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-io-role l d (ksHead (KA.stServer c)) {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decKAs-io-role l d (ksHead (KA.stServer c)) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-io-role l d (ksHead (KA.stServer c)) {e₁ = KA.apiKAev l' d' m} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-io-role l d (ksHead (KA.stServer c)) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-io-role l d (ksHead KA.stDone) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAs-io-role l d (ksRecv1 c) {e₁ = KA.apiKAev l' d' m} {a} s with step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s
... | offer with KA.KAEv-≟ (_ , KA.apiKAev l d recvKACookie) (_ , KA.apiKAev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = tt
decKAs-io-role l d (ksRecv1 c) {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-io-role l d (ksRecv1 c) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-io-role l d (ksRecv1 c) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-io-role l d ksDdone1 {e₁ = KA.doneKA l' d'} {a} s with step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s
... | offer with KA.KAEv-≟ (_ , KA.doneKA l d) (_ , KA.doneKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = tt
decKAs-io-role l d ksDdone1 {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-io-role l d ksDdone1 {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-io-role l d ksDdone1 {e₁ = KA.apiKAev l' d' m} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-io-role l d (ksSil st) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decTSc-src-dir (item 3a): the fired event's value
-- carries the peer's client role (msgOrigin); non-io firings give ⊤.
decTSc-io-role : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : TSProc}
  → decTSc-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e₁ a)) ]─► P′
  → ClientIo (ιTS e₁) a
-- head stInit : sends MsgTSInit (io) → tcSil stIdle
decTSc-io-role l d (tcHead TS.stInit) {e₁ = TS.sendTS l' d'} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-io-role l d (tcHead TS.stInit) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
decTSc-io-role l d (tcHead TS.stInit) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
decTSc-io-role l d (tcHead TS.stInit) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
-- head stIdle : receives a wire request → tcReqIdsB1 / tcReqIdsNB1 / tcReqTxs1
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking a r)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking a r)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxs ids)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit}        s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone}        s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-io-role l d (tcHead TS.stIdle) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
-- head stTxIdsBlocking : fires apiTSev sendTSReplyTxIds / sendTSDone
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSDone} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}          s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
-- head stTxIdsNonBlocking : fires apiTSev sendTSReplyTxIds
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSDone}                 s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}          s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-io-role l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
-- head stTxs : fires apiTSev sendTSReplyTxs
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSReplyTxs} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSDone}                  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}           s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-io-role l d (tcHead TS.stTxs) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
-- head stDone : ret, no visible step
decTSc-io-role l d (tcHead TS.stDone) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaf tcReqIdsB1 : fires apiTSev recvTSRequestTxIds (Blocking,a,r) → tcSil stTxIdsBlocking
decTSc-io-role l d (tcReqIdsB1 a r) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxIds) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (Blocking , a , r)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decTSc-io-role l d (tcReqIdsB1 a r) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
decTSc-io-role l d (tcReqIdsB1 a r) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
decTSc-io-role l d (tcReqIdsB1 a r) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
-- recv leaf tcReqIdsNB1 : fires apiTSev recvTSRequestTxIds (NonBlocking,a,r) → tcSil stTxIdsNonBlocking
decTSc-io-role l d (tcReqIdsNB1 a r) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxIds) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (NonBlocking , a , r)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decTSc-io-role l d (tcReqIdsNB1 a r) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
decTSc-io-role l d (tcReqIdsNB1 a r) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
decTSc-io-role l d (tcReqIdsNB1 a r) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
-- recv leaf tcReqTxs1 : fires apiTSev recvTSRequestTxs ids → tcSil stTxs
decTSc-io-role l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxs) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec (λ _ _ → yes refl) val ids
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decTSc-io-role l d (tcReqTxs1 ids) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
decTSc-io-role l d (tcReqTxs1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
decTSc-io-role l d (tcReqTxs1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
-- send leaf tcRepB1 : fires sendTS (MsgTSReplyTxIds ids) → tcSil stIdle
decTSc-io-role l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-io-role l d (tcRepB1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
decTSc-io-role l d (tcRepB1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
decTSc-io-role l d (tcRepB1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
-- send leaf tcDone1 : fires sendTS MsgTSDone → tcSil stDone
decTSc-io-role l d tcDone1 {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-io-role l d tcDone1 {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
decTSc-io-role l d tcDone1 {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
decTSc-io-role l d tcDone1 {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
-- send leaf tcRepNB1 : fires sendTS (MsgTSReplyTxIds ids) → tcSil stIdle
decTSc-io-role l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-io-role l d (tcRepNB1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
decTSc-io-role l d (tcRepNB1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
decTSc-io-role l d (tcRepNB1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
-- send leaf tcRepTxs1 : fires sendTS (MsgTSReplyTxs txs) → tcSil stIdle
decTSc-io-role l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-io-role l d (tcRepTxs1 txs) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
decTSc-io-role l d (tcRepTxs1 txs) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
decTSc-io-role l d (tcRepTxs1 txs) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
-- loop re-entry : sil, no visible step
decTSc-io-role l d (tcSil st) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decTSs-src-dir (item 3a): the fired event's value
-- carries the peer's server role (msgOrigin); non-io firings give ⊤.
decTSs-io-role : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : TSProc}
  → decTSs-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e₁ a)) ]─► P′
  → ServerIo (ιTS e₁) a
-- head stInit : receives MsgTSInit → tsSil stIdle
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSInit} s with step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-io-role l d (tsHead TS.stInit) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
-- head stIdle : fires the three api pull requests
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSDone}       s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-io-role l d (tsHead TS.stIdle) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
-- head stTxIdsBlocking : receives MsgTSReplyTxIds (→ tsSil stIdle) / MsgTSDone (→ tsDone1)
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSDone} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
-- head stTxIdsNonBlocking : receives MsgTSReplyTxIds → tsSil stIdle
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-io-role l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
-- head stTxs : receives MsgTSReplyTxs → tsSil stIdle
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxs txs)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-io-role l d (tsHead TS.stTxs) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
-- head stDone : ret, no visible step
decTSs-io-role l d (tsHead TS.stDone) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf tsDone1 : fires doneTS → tsSil stDone
decTSs-io-role l d tsDone1 {e₁ = TS.doneTS l' d'} {a} s with step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s
... | offer with TS.TSEv-≟ (_ , TS.doneTS l d) (_ , TS.doneTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = tt
decTSs-io-role l d tsDone1 {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
decTSs-io-role l d tsDone1 {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
decTSs-io-role l d tsDone1 {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
-- send leaf tsReqB1 : fires sendTS (MsgTSRequestTxIds Blocking a r) → tsSil stTxIdsBlocking
decTSs-io-role l d (tsReqB1 (a , r)) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSs-io-role l d (tsReqB1 (a , r)) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
decTSs-io-role l d (tsReqB1 (a , r)) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
decTSs-io-role l d (tsReqB1 (a , r)) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
-- send leaf tsReqNB1 : fires sendTS (MsgTSRequestTxIds NonBlocking a r) → tsSil stTxIdsNonBlocking
decTSs-io-role l d (tsReqNB1 (a , r)) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSs-io-role l d (tsReqNB1 (a , r)) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
decTSs-io-role l d (tsReqNB1 (a , r)) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
decTSs-io-role l d (tsReqNB1 (a , r)) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
-- send leaf tsReqTxs1 : fires sendTS (MsgTSRequestTxs ids) → tsSil stTxs
decTSs-io-role l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSs-io-role l d (tsReqTxs1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
decTSs-io-role l d (tsReqTxs1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
decTSs-io-role l d (tsReqTxs1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
-- loop re-entry : sil, no visible step
decTSs-io-role l d (tsSil st) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decLNc-src-dir (item 3a): the fired event's value
-- carries the peer's client role (msgOrigin); non-io firings give ⊤.
decLNc-io-role : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : LNProc}
  → decLNc-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e₁ a)) ]─► P′
  → ClientIo (ιLN e₁) a
-- head stIdle : fires apiLNev sendLNRequestNext / sendLNDone
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNRequestNext} {a} s with step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNDone} {a} s with step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockTxsOffer}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNVotesOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockTxsOffer}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNVotesOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-io-role l d (lncHead LNp.stIdle) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
-- head stBusy : receives one of four notifications
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockOffer q)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNRequestNext} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNDone} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-io-role l d (lncHead LNp.stBusy) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
-- head stDone : ret, no visible step
decLNc-io-role l d (lncHead LNp.stDone) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaf lncRann1 : fires apiLNev recvLNBlockAnnouncement h → lncSil stIdle
decLNc-io-role l d (lncRann1 h) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockAnnouncement) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ h
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decLNc-io-role l d (lncRann1 h) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
decLNc-io-role l d (lncRann1 h) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
decLNc-io-role l d (lncRann1 h) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
-- recv leaf lncRoff1 : fires apiLNev recvLNBlockOffer q → lncSil stIdle
decLNc-io-role l d (lncRoff1 q) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ q
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decLNc-io-role l d (lncRoff1 q) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
decLNc-io-role l d (lncRoff1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
decLNc-io-role l d (lncRoff1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
-- recv leaf lncRtxs1 : fires apiLNev recvLNBlockTxsOffer q → lncSil stIdle
decLNc-io-role l d (lncRtxs1 q) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockTxsOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ q
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decLNc-io-role l d (lncRtxs1 q) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
decLNc-io-role l d (lncRtxs1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
decLNc-io-role l d (lncRtxs1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
-- recv leaf lncRvot1 : fires apiLNev recvLNVotesOffer vs → lncSil stIdle
decLNc-io-role l d (lncRvot1 vs) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNVotesOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val vs
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decLNc-io-role l d (lncRvot1 vs) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
decLNc-io-role l d (lncRvot1 vs) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
decLNc-io-role l d (lncRvot1 vs) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
-- send leaf lncReq1 : fires sendLN MsgLNRequestNext → lncSil stBusy
decLNc-io-role l d lncReq1 {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-io-role l d lncReq1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
decLNc-io-role l d lncReq1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
decLNc-io-role l d lncReq1 {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
-- send leaf lncDone1 : fires sendLN MsgLNDone → lncSil stDone
decLNc-io-role l d lncDone1 {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-io-role l d lncDone1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
decLNc-io-role l d lncDone1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
decLNc-io-role l d lncDone1 {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
-- loop re-entry : sil, no visible step
decLNc-io-role l d (lncSil st) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decLNs-src-dir (item 3a): the fired event's value
-- carries the peer's server role (msgOrigin); non-io firings give ⊤.
decLNs-io-role : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : LNProc}
  → decLNs-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e₁ a)) ]─► P′
  → ServerIo (ιLN e₁) a
-- head stIdle : receives MsgLNRequestNext (→ lnsSil stBusy) / MsgLNDone (→ lnsDone1)
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNRequestNext} s with step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNDone} s with step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-io-role l d (lnsHead LNp.stIdle) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
-- head stBusy : fires one of four api sends
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockAnnouncement} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockTxsOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNVotesOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNRequestNext} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNDone}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockOffer}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockTxsOffer} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNVotesOffer}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-io-role l d (lnsHead LNp.stBusy) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
-- head stDone : ret, no visible step
decLNs-io-role l d (lnsHead LNp.stDone) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf lnsDone1 : fires doneLN → lnsSil stDone
decLNs-io-role l d lnsDone1 {e₁ = LNp.doneLN l' d'} {a} s with step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.doneLN l d) (_ , LNp.doneLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = tt
decLNs-io-role l d lnsDone1 {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
decLNs-io-role l d lnsDone1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
decLNs-io-role l d lnsDone1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
-- send leaf lnsWann1 : fires sendLN (MsgLNBlockAnnouncement h) → lnsSil stIdle
decLNs-io-role l d (lnsWann1 h) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-io-role l d (lnsWann1 h) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
decLNs-io-role l d (lnsWann1 h) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
decLNs-io-role l d (lnsWann1 h) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
-- send leaf lnsWoff1 : fires sendLN (MsgLNBlockOffer q) → lnsSil stIdle
decLNs-io-role l d (lnsWoff1 q) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-io-role l d (lnsWoff1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
decLNs-io-role l d (lnsWoff1 q) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
decLNs-io-role l d (lnsWoff1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
-- send leaf lnsWtxs1 : fires sendLN (MsgLNBlockTxsOffer q) → lnsSil stIdle
decLNs-io-role l d (lnsWtxs1 q) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-io-role l d (lnsWtxs1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
decLNs-io-role l d (lnsWtxs1 q) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
decLNs-io-role l d (lnsWtxs1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
-- send leaf lnsWvot1 : fires sendLN (MsgLNVotesOffer vs) → lnsSil stIdle
decLNs-io-role l d (lnsWvot1 vs) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-io-role l d (lnsWvot1 vs) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
decLNs-io-role l d (lnsWvot1 vs) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
decLNs-io-role l d (lnsWvot1 vs) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
-- loop re-entry : sil, no visible step
decLNs-io-role l d (lnsSil st) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decLFc-src-dir (item 3a): the fired event's value
-- carries the peer's client role (msgOrigin); non-io firings give ⊤.
decLFc-io-role : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : LFProc}
  → decLFc-src l d pos LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e₁ a)) ]─► P′
  → ClientIo (ιLF e₁) a
-- head stIdle : five api requests
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFDone} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-io-role l d (lfcHead LFp.stIdle) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
-- head stBlock / stBlockTxs / stVotes / stBlockRange : wire receives
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlock b)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlock) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stVotes) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-io-role l d (lfcHead LFp.stBlockRange) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
-- head stDone : ret
decLFc-io-role l d (lfcHead LFp.stDone) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaves
decLFc-io-role l d (lfcRblk1 b) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decLFc-io-role l d (lfcRblk1 b) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-io-role l d (lfcRblk1 b) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-io-role l d (lfcRblk1 b) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-io-role l d (lfcRbtx1 ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFBlockTxs) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val ts
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decLFc-io-role l d (lfcRbtx1 ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-io-role l d (lfcRbtx1 ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-io-role l d (lfcRbtx1 ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-io-role l d (lfcRvot1 vs) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFVoteDelivery) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val vs
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decLFc-io-role l d (lfcRvot1 vs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-io-role l d (lfcRvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-io-role l d (lfcRvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-io-role l d (lfcRnext1 b ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFRangeBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEqI.DecEq-× ⦄ val (b , ts)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decLFc-io-role l d (lfcRnext1 b ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-io-role l d (lfcRnext1 b ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-io-role l d (lfcRnext1 b ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-io-role l d (lfcRlast1 b ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFRangeBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEqI.DecEq-× ⦄ val (b , ts)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tt
decLFc-io-role l d (lfcRlast1 b ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
decLFc-io-role l d (lfcRlast1 b ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
decLFc-io-role l d (lfcRlast1 b ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
-- send leaves
decLFc-io-role l d (lfcWblk1 pt) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-io-role l d (lfcWblk1 pt) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-io-role l d (lfcWblk1 pt) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-io-role l d (lfcWblk1 pt) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-io-role l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-io-role l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-io-role l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-io-role l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-io-role l d (lfcWvot1 vs) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-io-role l d (lfcWvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-io-role l d (lfcWvot1 vs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-io-role l d (lfcWvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-io-role l d (lfcWrng1 r) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-io-role l d (lfcWrng1 r) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-io-role l d (lfcWrng1 r) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-io-role l d (lfcWrng1 r) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-io-role l d lfcDone1 {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-io-role l d lfcDone1 {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
decLFc-io-role l d lfcDone1 {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
decLFc-io-role l d lfcDone1 {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
-- loop re-entry
decLFc-io-role l d (lfcSil st) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- io-role transform of decLFs-src-dir (item 3a): the fired event's value
-- carries the peer's server role (msgOrigin); non-io firings give ⊤.
decLFs-io-role : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : LFProc}
  → decLFs-src l d pos LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e₁ a)) ]─► P′
  → ServerIo (ιLF e₁) a
-- head stIdle : five wire requests (4 loops + done)
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFDone)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-io-role l d (lfsHead LFp.stIdle) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
-- head stBlock / stBlockTxs / stVotes / stBlockRange : api sends
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlock} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlock) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stVotes) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tt
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-io-role l d (lfsHead LFp.stBlockRange) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
-- head stDone : ret
decLFs-io-role l d (lfsHead LFp.stDone) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf
decLFs-io-role l d lfsDone1 {e₁ = LFp.doneLF l' d'} {a} s with step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s
... | offer with LFp.LFEv-≟ (_ , LFp.doneLF l d) (_ , LFp.doneLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = tt
decLFs-io-role l d lfsDone1 {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
decLFs-io-role l d lfsDone1 {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
decLFs-io-role l d lfsDone1 {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
-- send leaves
decLFs-io-role l d (lfsWblk1 b) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-io-role l d (lfsWblk1 b) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-io-role l d (lfsWblk1 b) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-io-role l d (lfsWblk1 b) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-io-role l d (lfsWtxs1 ts) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-io-role l d (lfsWtxs1 ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-io-role l d (lfsWtxs1 ts) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-io-role l d (lfsWtxs1 ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-io-role l d (lfsWvot1 vs) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-io-role l d (lfsWvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-io-role l d (lfsWvot1 vs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-io-role l d (lfsWvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-io-role l d (lfsWnext1 (b , ts)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-io-role l d (lfsWnext1 (b , ts)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-io-role l d (lfsWnext1 (b , ts)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-io-role l d (lfsWnext1 (b , ts)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-io-role l d (lfsWlast1 (b , ts)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-io-role l d (lfsWlast1 (b , ts)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
decLFs-io-role l d (lfsWlast1 (b , ts)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
decLFs-io-role l d (lfsWlast1 (b , ts)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
-- loop re-entry
decLFs-io-role l d (lfsSil st) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

------------------------------------------------------------------------
-- ITEM 3b (part 1) — augmented io-sims.  Bridge a renamed per-peer step
-- `decXc/Xs l d pos ─[ev e a]─►` back to the source step (via the RenTC
-- `XNO.renameMap-ev-reflect-ι` reflect), then read off BOTH the fired
-- direction (`decXc/Xs-src-dir`) and the value-role (`decXc/Xs-io-role`).
-- The io content of the bundle role-peel; `bundleG-io-role` plumbs these.
------------------------------------------------------------------------

-- CS client augmented io-sim
simCSc-io : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ CS.CSEv X ] (e ≡ ιCS e₁) × (csEvDir e₁ ≡ d) × ClientIo (ιCS e₁) a
simCSc-io l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιCS-inv-shape iota , decCSc-src-dir l d pos srcStep , decCSc-io-role l d pos srcStep

-- CS server augmented io-sim
simCSs-io : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ CS.CSEv X ] (e ≡ ιCS e₁) × (csEvDir e₁ ≡ d) × ServerIo (ιCS e₁) a
simCSs-io l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιCS-inv-shape iota , decCSs-src-dir l d pos srcStep , decCSs-io-role l d pos srcStep

-- BF client augmented io-sim
simBFc-io : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ BF.BFEv X ] (e ≡ ιBF e₁) × (bfEvDir e₁ ≡ d) × ClientIo (ιBF e₁) a
simBFc-io l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιBF-inv-shape iota , decBFc-src-dir l d pos srcStep , decBFc-io-role l d pos srcStep

-- BF server augmented io-sim
simBFs-io : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ BF.BFEv X ] (e ≡ ιBF e₁) × (bfEvDir e₁ ≡ d) × ServerIo (ιBF e₁) a
simBFs-io l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιBF-inv-shape iota , decBFs-src-dir l d pos srcStep , decBFs-io-role l d pos srcStep

-- KA client augmented io-sim
simKAc-io : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decKAc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ KA.KAEv X ] (e ≡ ιKA e₁) × (kaEvDir e₁ ≡ d) × ClientIo (ιKA e₁) a
simKAc-io l d pos step with KANO.renameMap-ev-reflect-ι {P = decKAc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιKA-inv-shape iota , decKAc-src-dir l d pos srcStep , decKAc-io-role l d pos srcStep

-- KA server augmented io-sim
simKAs-io : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decKAs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ KA.KAEv X ] (e ≡ ιKA e₁) × (kaEvDir e₁ ≡ d) × ServerIo (ιKA e₁) a
simKAs-io l d pos step with KANO.renameMap-ev-reflect-ι {P = decKAs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιKA-inv-shape iota , decKAs-src-dir l d pos srcStep , decKAs-io-role l d pos srcStep

-- TS client augmented io-sim (role-inverted protocol; roles come from msgOrigin)
simTSc-io : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decTSc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ TS.TSEv X ] (e ≡ ιTS e₁) × (tsEvDir e₁ ≡ d) × ClientIo (ιTS e₁) a
simTSc-io l d pos step with TSNO.renameMap-ev-reflect-ι {P = decTSc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιTS-inv-shape iota , decTSc-src-dir l d pos srcStep , decTSc-io-role l d pos srcStep

-- TS server augmented io-sim
simTSs-io : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decTSs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ TS.TSEv X ] (e ≡ ιTS e₁) × (tsEvDir e₁ ≡ d) × ServerIo (ιTS e₁) a
simTSs-io l d pos step with TSNO.renameMap-ev-reflect-ι {P = decTSs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιTS-inv-shape iota , decTSs-src-dir l d pos srcStep , decTSs-io-role l d pos srcStep

-- LN client augmented io-sim
simLNc-io : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decLNc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ LNp.LNEv X ] (e ≡ ιLN e₁) × (lnEvDir e₁ ≡ d) × ClientIo (ιLN e₁) a
simLNc-io l d pos step with LNNO.renameMap-ev-reflect-ι {P = decLNc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιLN-inv-shape iota , decLNc-src-dir l d pos srcStep , decLNc-io-role l d pos srcStep

-- LN server augmented io-sim
simLNs-io : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decLNs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ LNp.LNEv X ] (e ≡ ιLN e₁) × (lnEvDir e₁ ≡ d) × ServerIo (ιLN e₁) a
simLNs-io l d pos step with LNNO.renameMap-ev-reflect-ι {P = decLNs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιLN-inv-shape iota , decLNs-src-dir l d pos srcStep , decLNs-io-role l d pos srcStep

-- LF client augmented io-sim
simLFc-io : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decLFc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ LFp.LFEv X ] (e ≡ ιLF e₁) × (lfEvDir e₁ ≡ d) × ClientIo (ιLF e₁) a
simLFc-io l d pos step with LFNO.renameMap-ev-reflect-ι {P = decLFc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιLF-inv-shape iota , decLFc-src-dir l d pos srcStep , decLFc-io-role l d pos srcStep

-- LF server augmented io-sim
simLFs-io : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decLFs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ LFp.LFEv X ] (e ≡ ιLF e₁) × (lfEvDir e₁ ≡ d) × ServerIo (ιLF e₁) a
simLFs-io l d pos step with LFNO.renameMap-ev-reflect-ι {P = decLFs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq =
      e₁ , ιLF-inv-shape iota , decLFs-src-dir l d pos srcStep , decLFs-io-role l d pos srcStep

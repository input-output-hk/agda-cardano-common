{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 — io-peel layer, PART 3 (RAM split of SysIoLink2).
-- ITEM-3-ABSTRACT: the ABSTRACT-side (tableSpec) io-role inversions — the
-- analog of the concrete decXc/Xs-io-role + bundleG-io-role + nodeX-io-fp,
-- but over the τ-free `tableSpec` abstract peers (NOT renameMap-renamed).
-- Feeds `top-nodes-io` / `comove-io-sync` the abstract nodes' shared-link
-- sibling (dir,role) fingerprint so the make-or-break evBoth is refuted on
-- the abstract side too.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink3 where

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
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; Block₃; b1; produce )
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
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium
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
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( decNodeB; decNodeC; decNodeD; bundleG; decCP; decConsD
        ; consD; consuming; producing
        -- the two straight-chain drivers + their phase enumerations
        ; decProd; decCons; ProdPh; ConsPh
        ; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        -- the renamed-peer sources (for the concrete bundle break-non-offer)
        ; decCSc-src; decCSs-src; decBFc-src; decBFs-src )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode as SN
-- the per-protocol process-type synonyms (the `{P′ : XProc}` sig fields of item 3a)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( CSProc; BFProc; KAProc; TSProc; LNProc; LFProc )
-- the τ-free peer interpreter (`tableSpec`) + abstract positions/tables + the
-- inert KA/TS specs (for the ABSTRACT bundle break non-offer, `absBundleG` side)
import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs as NS

-- the Net_Api prefix (`⟶₀`) visible-step inversion (for the role discriminator)
import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) as PInv
open PInv using ( ⟶₀-ev-inv )
-- abstract node decodes + the abstract bundle + the io-offer predicate
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep
  using ( absNodeA; absNodeB; absNodeC; absNodeD; absBundleG; IoOffers )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep as SStep
-- the whole-system concrete decode + config record (for the top-level api peel)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
-- the shared io-hide alphabet (api events are disjoint from it)
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode using ( LFProc )
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


-- KA api-tag constructors (used as patterns in the kaCnxt/kaSnxt tables; an
-- unimported tag would become a silent pattern variable and stick the table)
open import CSP.Examples.Cardano_network.Net p using
  ( sendKAMsg; sendKADone; errCookie; recvKACookie )
-- TS / LN api-tag constructors (same reason — the item-3a-rest CS/BF/TS/LN/LF
-- tables pattern on these; unimported = silent pattern var = stuck table)
open import CSP.Examples.Cardano_network.Net p using
  ( sendTSReplyTxIds; sendTSReplyTxs; sendTSDone; recvTSRequestTxIds; recvTSRequestTxs
  ; sendTSRequestTxIdsBlocking; sendTSRequestTxIdsPipelined; sendTSRequestTxsPipelined
  ; sendLNRequestNext; sendLNBlockAnnouncement; sendLNBlockOffer; sendLNBlockTxsOffer
  ; sendLNVotesOffer; sendLNDone; recvLNBlockAnnouncement; recvLNBlockOffer
  ; recvLNBlockTxsOffer; recvLNVotesOffer )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink2 public
-- ιKA/ιTS/ιLN reach lower modules only via body-level import → re-import here
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιKA; ιTS; ιLN )
-- the abstract per-peer tableSpec decodes + their head-collapse coarsenings
-- (a plain `open` in SysIoLink does NOT re-export through the public chain)
open SStep using
  ( absKAc; absKAs; absCSc; absCSs; absBFc; absBFs
  ; absTSc; absTSs; absLNc; absLNs; absLFc; absLFs
  ; coarsenKAc; coarsenKAs; coarsenCSc; coarsenCSs; coarsenBFc; coarsenBFs
  ; coarsenTSc; coarsenTSs; coarsenLNc; coarsenLNs; coarsenLFc; coarsenLFs )

------------------------------------------------------------------------
-- ITEM-3a-ABSTRACT (KA) — the abstract tableSpec io-role fingerprints.
--
-- For each abstract peer `absXc/Xs l d q = tableSpec … (coarsenX q)` a visible
-- step inverts (via `tableSpec-ev-inv`) to a firing `nxt`-table edge; the table
-- lemma `xCnxt/Snxt-io-role` reads off BOTH the direction (`xEvDir e₁ ≡ d`,
-- forced by the `d′ ≟ d` guard) and the value-role (`Client/ServerIo (ιX e₁) a`,
-- forced by the payload `≟`-gate — a client `!`-send is `FromInitiator`, a
-- server `!`-send is `FromResponder`, api/done events give `⊤`).  This is the
-- abstract analog of the concrete `decXc/Xs-io-role` + `simXc/Xs-io`, but over
-- `tableSpec` (NOT the renameMap image), so it feeds `mkInjC/mkInjS` at `iota
-- = refl` (the peel already fixes `e = ιX e₁`).
------------------------------------------------------------------------

-- KA-client abstract io-role table lemma (dir + value-role of a firing edge)
kaCnxt-io-role : (l : Link) (d : Dir) (q : NS.KAcPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X} {q′ : NS.KAcPos}
  → NS.kaCnxt l d q (X , ιKA e₁) a ≡ just q′
  → (kaEvDir e₁ ≡ d) × ClientIo (ιKA e₁) a
-- kcClient : fires apiKA sendKAMsg / sendKADone (api ⇒ ⊤)
kaCnxt-io-role l d NS.kcClient (KA.apiKAev l' d' sendKAMsg) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcClient (KA.apiKAev l' d' sendKADone) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcClient (KA.apiKAev l' d' errCookie) eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcClient (KA.apiKAev l' d' recvKACookie) eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcClient (KA.sendKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcClient (KA.receiveKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcClient (KA.doneKA l' d') eq = ⊥-elim (nothing-absurd eq)
-- kcWmsg c : fires sendKA (input) with FromInitiator MsgKeepAlive c (io ⇒ refl)
kaCnxt-io-role l d (NS.kcWmsg c) (KA.sendKA l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcWmsg c) (KA.sendKA l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcWmsg c) (KA.sendKA l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcWmsg c) (KA.receiveKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcWmsg c) (KA.apiKAev l' d' m) eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcWmsg c) (KA.doneKA l' d') eq = ⊥-elim (nothing-absurd eq)
-- kcWdone : fires sendKA (input) with FromInitiator MsgKADone (io ⇒ refl)
kaCnxt-io-role l d NS.kcWdone (KA.sendKA l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcWdone (KA.sendKA l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcWdone (KA.sendKA l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcWdone (KA.receiveKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcWdone (KA.apiKAev l' d' m) eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcWdone (KA.doneKA l' d') eq = ⊥-elim (nothing-absurd eq)
-- kcAwait c : fires receiveKA (output) with FromResponder MsgKeepAliveResponse (io ⇒ refl)
-- both `c ≟ c'` outcomes give a `just` edge, so the table fires either way and
-- the value-role/dir are read off the shape/guard — no need to split `c ≟ c'`
-- (a Cookie `≟`, whose instance would not align with the table's baked-in one)
kaCnxt-io-role l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAliveResponse c')} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAlive _)} eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , keepAlive MsgKADone} eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , chainSync _} eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.sendKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.apiKAev l' d' m) eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcAwait c) (KA.doneKA l' d') eq = ⊥-elim (nothing-absurd eq)
-- kcErr cq cr : fires apiKA errCookie (api ⇒ ⊤)
-- api event ⇒ role is ⊤ regardless of the `a ≟ (cq , cr)` gate, so we do not
-- split it (a Cookie² `≟`, instance would not align with the table's)
kaCnxt-io-role l d (NS.kcErr cq cr) (KA.apiKAev l' d' errCookie) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | _ = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcErr cq cr) (KA.apiKAev l' d' sendKAMsg) eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcErr cq cr) (KA.apiKAev l' d' sendKADone) eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcErr cq cr) (KA.apiKAev l' d' recvKACookie) eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcErr cq cr) (KA.sendKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcErr cq cr) (KA.receiveKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d (NS.kcErr cq cr) (KA.doneKA l' d') eq = ⊥-elim (nothing-absurd eq)
-- kcTerm / kcTermE : terminal (catch-all nothing)
kaCnxt-io-role l d NS.kcTerm e₁ eq = ⊥-elim (nothing-absurd eq)
kaCnxt-io-role l d NS.kcTermE e₁ eq = ⊥-elim (nothing-absurd eq)

-- KA-server abstract io-role table lemma (dir + value-role of a firing edge)
kaSnxt-io-role : (l : Link) (d : Dir) (q : NS.KAsPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X} {q′ : NS.KAsPos}
  → NS.kaSnxt l d q (X , ιKA e₁) a ≡ just q′
  → (kaEvDir e₁ ≡ d) × ServerIo (ιKA e₁) a
-- ksClient : receives MsgKeepAlive c / MsgKADone (output; FromInitiator ⇒ refl)
kaSnxt-io-role l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAlive c)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | _ = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , keepAlive MsgKADone} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | _ = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , chainSync _} eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.sendKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.apiKAev l' d' m) eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksClient (KA.doneKA l' d') eq = ⊥-elim (nothing-absurd eq)
-- ksRecv c : fires apiKA recvKACookie (api ⇒ ⊤)
-- api event ⇒ role is ⊤ regardless of the `a ≟ c` gate, so we do not split it
-- (a Cookie `≟`, instance would not align with the table's)
kaSnxt-io-role l d (NS.ksRecv c) (KA.apiKAev l' d' recvKACookie) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | _ = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksRecv c) (KA.apiKAev l' d' sendKAMsg) eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksRecv c) (KA.apiKAev l' d' sendKADone) eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksRecv c) (KA.apiKAev l' d' errCookie) eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksRecv c) (KA.sendKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksRecv c) (KA.receiveKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksRecv c) (KA.doneKA l' d') eq = ⊥-elim (nothing-absurd eq)
-- ksResp c : fires sendKA (input) with FromResponder MsgKeepAliveResponse c (io ⇒ refl)
kaSnxt-io-role l d (NS.ksResp c) (KA.sendKA l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksResp c) (KA.sendKA l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksResp c) (KA.sendKA l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksResp c) (KA.receiveKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksResp c) (KA.apiKAev l' d' m) eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d (NS.ksResp c) (KA.doneKA l' d') eq = ⊥-elim (nothing-absurd eq)
-- ksDdone : fires doneKA (done ⇒ ⊤)
kaSnxt-io-role l d NS.ksDdone (KA.doneKA l' d') eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | _ = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksDdone (KA.sendKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksDdone (KA.receiveKA l' d') eq = ⊥-elim (nothing-absurd eq)
kaSnxt-io-role l d NS.ksDdone (KA.apiKAev l' d' m) eq = ⊥-elim (nothing-absurd eq)
-- ksTerm : terminal (catch-all nothing)
kaSnxt-io-role l d NS.ksTerm e₁ eq = ⊥-elim (nothing-absurd eq)

-- KA-client abstract peer io-role (dir + client value-role from a visible step)
absKAc-io : (l : Link) (d : Dir) (q : KAcPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → absKAc l d q ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → (kaEvDir e₁ ≡ d) × ClientIo (ιKA e₁) a
absKAc-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d }) (coarsenKAc q) step
... | (q′ , nxtEq , _) = kaCnxt-io-role l d (coarsenKAc q) e₁ {a} nxtEq

-- KA-server abstract peer io-role (dir + server value-role from a visible step)
absKAs-io : (l : Link) (d : Dir) (q : KAsPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → absKAs l d q ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → (kaEvDir e₁ ≡ d) × ServerIo (ιKA e₁) a
absKAs-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d }) (coarsenKAs q) step
... | (q′ , nxtEq , _) = kaSnxt-io-role l d (coarsenKAs q) e₁ {a} nxtEq

------------------------------------------------------------------------
-- ITEM-3b-ABSTRACT (KA) — the abstract bundle io-role lift.  Inverse peel of
-- the 12-peer `absBundleG` at a KA-image event: the driven KA-client/server
-- gives the (dir,role) via `absKAc/KAs-io` + `mkInjC/mkInjS`; every sibling is
-- a NON-offer — the same-protocol opposite-role peer by the direction clash
-- (`absKAs/KAc-dir-noBoth`, the make-or-break abstract evBoth refute), the ten
-- foreign peers by the committed cross-protocol `absX-noKA` leaves.
------------------------------------------------------------------------

-- absBundleKA-io-role : role fingerprint of a KA-image abstract bundle io step
absBundleKA-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► Bd′
  → (dirOf (ιKA e₁) ≡ cl × ClientIo (ιKA e₁) a) ⊎ (dirOf (ιKA e₁) ≡ sv × ServerIo (ιKA e₁) a)
absBundleKA-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = inj₁ (mkInjC ιKA kaEvDir kaDirOf-ι (e₁ , refl , proj₁ (absKAc-io l cl (kac ip) sM) , proj₂ (absKAc-io l cl (kac ip) sM)))
... | PEA.evBoth _ sM sTail =
        ⊥-elim (SStep.⦀-noOffer (absKAs l sv (kas ip)) _
                  (absKAs-dir-noBoth l sv (kas ip) e₁ (λ q → cl≢sv (trans (sym (proj₁ (absKAc-io l cl (kac ip) sM))) q)))
                  (SStep.⦀-noOffer (absCSc l cl csc) _ (absCSc-noKA l cl csc e₁)
                   (SStep.⦀-noOffer (absCSs l sv css) _ (absCSs-noKA l sv css e₁)
                    (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noKA l cl bfc e₁)
                     (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noKA l sv bfs e₁)
                      (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noKA l cl (tsc ip) e₁)
                       (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noKA l sv (tss ip) e₁)
                        (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noKA l cl (lnc ip) e₁)
                         (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noKA l sv (lns ip) e₁)
                          (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noKA l cl (lfc ip) e₁) (absLFs-noKA l sv (lfs ip) e₁))))))))))
                  (_ , sTail))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = inj₂ (mkInjS ιKA kaEvDir kaDirOf-ι (e₁ , refl , proj₁ (absKAs-io l sv (kas ip) sM) , proj₂ (absKAs-io l sv (kas ip) sM)))
...   | PEA.evBoth _ sM sTail =
          ⊥-elim (SStep.⦀-noOffer (absCSc l cl csc) _ (absCSc-noKA l cl csc e₁)
                   (SStep.⦀-noOffer (absCSs l sv css) _ (absCSs-noKA l sv css e₁)
                    (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noKA l cl bfc e₁)
                     (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noKA l sv bfs e₁)
                      (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noKA l cl (tsc ip) e₁)
                       (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noKA l sv (tss ip) e₁)
                        (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noKA l cl (lnc ip) e₁)
                         (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noKA l sv (lns ip) e₁)
                          (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noKA l cl (lfc ip) e₁) (absLFs-noKA l sv (lfs ip) e₁)))))))))
                  (_ , sTail))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = ⊥-elim (absCSc-noKA l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noKA l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = ⊥-elim (absCSs-noKA l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noKA l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = ⊥-elim (absBFc-noKA l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noKA l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = ⊥-elim (absBFs-noKA l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noKA l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (absTSc-noKA l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noKA l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (absTSs-noKA l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noKA l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (absLNc-noKA l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noKA l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (absLNs-noKA l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noKA l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (absLFc-noKA l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noKA l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (absLFs-noKA l sv (lfs ip) e₁ (_ , qs))

------------------------------------------------------------------------
-- ITEM-3a-ABSTRACT (rest) — CS/BF/TS/LN/LF abstract tableSpec io-role
-- fingerprints + peer wrappers.  Same transform as the KA slice: each
-- `xCnxt/Snxt-io-role` reads dir (from the `d′ ≟ d` guard) + value-role
-- (io-wire firing → refl via msgOrigin ; api/done → tt) off a firing NodeSpecs
-- table edge; `absXc/Xs-io` lifts via `tableSpec-ev-inv` at the coarse pos.
-- Mechanically generated from the committed `xCnxt/Snxt-dir-no` case trees.
------------------------------------------------------------------------

csCnxt-io-role : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X} {q′ : NS.CScPos}
  → NS.csCnxt l d q (X , ιCS e₁) a ≡ just q′
  → (csEvDir e₁ ≡ d) × ClientIo (ιCS e₁) a
csCnxt-io-role l d NS.ccIdle (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' sendCSRequestNext) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' sendCSFindIntersect) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' sendCSDone) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' sendCSAwaitReply) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' sendCSRollForward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' sendCSRollBackward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' recvCSRollforward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' recvCSRollback) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' reqCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.apiCSev l' d' reqCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccIdle (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWreq (CS.sendCS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWreq (CS.sendCS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWreq (CS.sendCS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWreq (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWreq (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWreq (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccAwait (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccWfi pts) (CS.sendCS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect pts))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccWfi pts) (CS.sendCS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccWfi pts) (CS.sendCS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccWfi _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccWfi _) (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccWfi _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccInt (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWdone (CS.sendCS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWdone (CS.sendCS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWdone (CS.sendCS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWdone (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWdone (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccWdone (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccMust (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' sendCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' sendCSDone) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' sendCSAwaitReply) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollForward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollBackward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollforward) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollback) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' reqCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.apiCSev l' d' reqCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArf _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' sendCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' sendCSDone) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' sendCSAwaitReply) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollForward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollBackward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollforward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollback) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' reqCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.apiCSev l' d' reqCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccArb _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' sendCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' sendCSDone) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' sendCSAwaitReply) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollForward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollBackward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollforward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollback) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectFound) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' reqCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.apiCSev l' d' reqCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAif _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' sendCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' sendCSDone) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' sendCSAwaitReply) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollForward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollBackward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollforward) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollback) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectNotFound) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' reqCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.apiCSev l' d' reqCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d (NS.ccAin _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccTerm (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccTerm (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccTerm (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csCnxt-io-role l d NS.ccTerm (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)

csSnxt-io-role : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X} {q′ : NS.CSsPos}
  → NS.csSnxt l d q (X , ιCS e₁) a ≡ just q′
  → (csEvDir e₁ ≡ d) × ServerIo (ιCS e₁) a
csSnxt-io-role l d NS.csIdle (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csIdle (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' sendCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' sendCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' sendCSDone) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' sendCSAwaitReply) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' sendCSRollForward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' sendCSRollBackward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' recvCSRollforward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' recvCSRollback) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' reqCSRequestNext) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.apiCSev l' d' reqCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csAreq (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' sendCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' sendCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' sendCSDone) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' sendCSAwaitReply) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollForward) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollBackward) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollforward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollback) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' reqCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.apiCSev l' d' reqCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csCanAwait (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' sendCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' sendCSDone) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' sendCSAwaitReply) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollForward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollBackward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollforward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollback) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' reqCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.apiCSev l' d' reqCSFindIntersect) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csAfi _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' sendCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' sendCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' sendCSDone) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' sendCSAwaitReply) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' sendCSRollForward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' sendCSRollBackward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' sendCSIntersectFound) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' sendCSIntersectNotFound) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' recvCSRollforward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' recvCSRollback) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' recvCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' recvCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' reqCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.apiCSev l' d' reqCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csInt (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csDdone (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csDdone (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csDdone (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csDdone (CS.doneCS l' d') eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' sendCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' sendCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' sendCSDone) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' sendCSAwaitReply) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' sendCSRollForward) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' sendCSRollBackward) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' sendCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' sendCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' recvCSRollforward) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' recvCSRollback) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' recvCSIntersectFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' recvCSIntersectNotFound) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' reqCSRequestNext) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.apiCSev l' d' reqCSFindIntersect) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csMust (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrf (h , tp)) (CS.sendCS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h tp))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrf (h , tp)) (CS.sendCS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrf (h , tp)) (CS.sendCS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrf _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrf _) (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrf _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrb (pt , tp)) (CS.sendCS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrb (pt , tp)) (CS.sendCS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrb (pt , tp)) (CS.sendCS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrb _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrb _) (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWrb _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csWar (CS.sendCS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csWar (CS.sendCS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csWar (CS.sendCS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csWar (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csWar (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csWar (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWif (pt , tp)) (CS.sendCS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWif (pt , tp)) (CS.sendCS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWif (pt , tp)) (CS.sendCS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWif _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWif _) (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWif _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWin tp) (CS.sendCS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWin tp) (CS.sendCS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWin tp) (CS.sendCS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWin _) (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWin _) (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d (NS.csWin _) (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csTerm (CS.sendCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csTerm (CS.receiveCS l' d') eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csTerm (CS.apiCSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
csSnxt-io-role l d NS.csTerm (CS.doneCS l' d') eq = ⊥-elim (nothing-absurd eq)

absCSc-io : (l : Link) (d : Dir) (q : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSc l d q ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → (csEvDir e₁ ≡ d) × ClientIo (ιCS e₁) a
absCSc-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d }) (coarsenCSc q) step
... | (q′ , nxtEq , _) = csCnxt-io-role l d (coarsenCSc q) e₁ {a} nxtEq

absCSs-io : (l : Link) (d : Dir) (q : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSs l d q ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → (csEvDir e₁ ≡ d) × ServerIo (ιCS e₁) a
absCSs-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d }) (coarsenCSs q) step
... | (q′ , nxtEq , _) = csSnxt-io-role l d (coarsenCSs q) e₁ {a} nxtEq

bfCnxt-io-role : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X} {q′ : NS.BFcPos}
  → NS.bfCnxt l d q (X , ιBF e₁) a ≡ just q′
  → (bfEvDir e₁ ≡ d) × ClientIo (ιBF e₁) a
bfCnxt-io-role l d NS.bcIdle (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.apiBFev l' d' sendBFRequestRange) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.apiBFev l' d' sendBFClientDone) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.apiBFev l' d' sendBFStartBatch) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.apiBFev l' d' sendBFNoBlocks) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.apiBFev l' d' sendBFBlock) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.apiBFev l' d' sendBFBatchDone) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.apiBFev l' d' recvBFBlock) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.apiBFev l' d' reqBFRange) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcIdle (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcWrr r) (BF.sendBF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcWrr r) (BF.sendBF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcWrr r) (BF.sendBF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcWrr _) (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcWrr _) (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcWrr _) (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcBusy (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcWcd (BF.sendBF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcWcd (BF.sendBF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcWcd (BF.sendBF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcWcd (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcWcd (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcWcd (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcStream (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFRequestRange) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFClientDone) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFStartBatch) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFNoBlocks) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBlock) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBatchDone) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.apiBFev l' d' recvBFBlock) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.apiBFev l' d' reqBFRange) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d (NS.bcAblk _) (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcTerm (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcTerm (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcTerm (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfCnxt-io-role l d NS.bcTerm (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)

bfSnxt-io-role : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X} {q′ : NS.BFsPos}
  → NS.bfSnxt l d q (X , ιBF e₁) a ≡ just q′
  → (bfEvDir e₁ ≡ d) × ServerIo (ιBF e₁) a
bfSnxt-io-role l d NS.bsIdle (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsIdle (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFRequestRange) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFClientDone) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFStartBatch) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFNoBlocks) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBlock) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBatchDone) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.apiBFev l' d' recvBFBlock) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.apiBFev l' d' reqBFRange) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsAreq _) (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.apiBFev l' d' sendBFRequestRange) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.apiBFev l' d' sendBFClientDone) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.apiBFev l' d' sendBFStartBatch) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.apiBFev l' d' sendBFNoBlocks) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.apiBFev l' d' sendBFBlock) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.apiBFev l' d' sendBFBatchDone) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.apiBFev l' d' recvBFBlock) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.apiBFev l' d' reqBFRange) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsBusy (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsDdone (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsDdone (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsDdone (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsDdone (BF.doneBF l' d') eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWsb (BF.sendBF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWsb (BF.sendBF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWsb (BF.sendBF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWsb (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWsb (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWsb (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.apiBFev l' d' sendBFRequestRange) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.apiBFev l' d' sendBFClientDone) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.apiBFev l' d' sendBFStartBatch) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.apiBFev l' d' sendBFNoBlocks) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.apiBFev l' d' sendBFBlock) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.apiBFev l' d' sendBFBatchDone) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.apiBFev l' d' recvBFBlock) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.apiBFev l' d' reqBFRange) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsStream (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWnb (BF.sendBF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWnb (BF.sendBF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWnb (BF.sendBF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWnb (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWnb (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWnb (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsWblk b) (BF.sendBF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsWblk b) (BF.sendBF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsWblk b) (BF.sendBF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsWblk _) (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsWblk _) (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d (NS.bsWblk _) (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWbd (BF.sendBF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWbd (BF.sendBF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWbd (BF.sendBF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWbd (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWbd (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsWbd (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsTerm (BF.sendBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsTerm (BF.receiveBF l' d') eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsTerm (BF.apiBFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
bfSnxt-io-role l d NS.bsTerm (BF.doneBF l' d') eq = ⊥-elim (nothing-absurd eq)

absBFc-io : (l : Link) (d : Dir) (q : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → absBFc l d q ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → (bfEvDir e₁ ≡ d) × ClientIo (ιBF e₁) a
absBFc-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d }) (coarsenBFc q) step
... | (q′ , nxtEq , _) = bfCnxt-io-role l d (coarsenBFc q) e₁ {a} nxtEq

absBFs-io : (l : Link) (d : Dir) (q : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → absBFs l d q ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → (bfEvDir e₁ ≡ d) × ServerIo (ιBF e₁) a
absBFs-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d }) (coarsenBFs q) step
... | (q′ , nxtEq , _) = bfSnxt-io-role l d (coarsenBFs q) e₁ {a} nxtEq

tsCnxt-io-role : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X} {q′ : NS.TScPos}
  → NS.tsCnxt l d q (X , ιTS e₁) a ≡ just q′
  → (tsEvDir e₁ ≡ d) × ClientIo (ιTS e₁) a
tsCnxt-io-role l d NS.tcInit (TS.sendTS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcInit (TS.sendTS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcInit (TS.sendTS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcInit (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcInit (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcInit (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSInit} eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSDone} eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.receiveTS l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcIdle (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l' d' sendTSReplyTxIds) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l' d' sendTSReplyTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l' d' sendTSDone) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l' d' sendTSRequestTxIdsBlocking) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l' d' sendTSRequestTxIdsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l' d' sendTSRequestTxsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l' d' recvTSRequestTxIds) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l' d' recvTSRequestTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (Blocking , a , r)) (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l' d' sendTSReplyTxIds) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l' d' sendTSReplyTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l' d' sendTSDone) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l' d' sendTSRequestTxIdsBlocking) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l' d' sendTSRequestTxIdsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l' d' sendTSRequestTxsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l' d' recvTSRequestTxIds) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l' d' recvTSRequestTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcAri (NonBlocking , a , r)) (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.apiTSev l' d' sendTSReplyTxIds) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.apiTSev l' d' sendTSReplyTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.apiTSev l' d' sendTSDone) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.apiTSev l' d' sendTSRequestTxIdsBlocking) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.apiTSev l' d' sendTSRequestTxIdsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.apiTSev l' d' sendTSRequestTxsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.apiTSev l' d' recvTSRequestTxIds) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.apiTSev l' d' recvTSRequestTxs) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcArt _) (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.apiTSev l' d' sendTSReplyTxIds) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.apiTSev l' d' sendTSReplyTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.apiTSev l' d' sendTSDone) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.apiTSev l' d' sendTSRequestTxIdsBlocking) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.apiTSev l' d' sendTSRequestTxIdsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.apiTSev l' d' sendTSRequestTxsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.apiTSev l' d' recvTSRequestTxIds) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.apiTSev l' d' recvTSRequestTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcBlk (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.apiTSev l' d' sendTSReplyTxIds) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.apiTSev l' d' sendTSReplyTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.apiTSev l' d' sendTSDone) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.apiTSev l' d' sendTSRequestTxIdsBlocking) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.apiTSev l' d' sendTSRequestTxIdsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.apiTSev l' d' sendTSRequestTxsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.apiTSev l' d' recvTSRequestTxIds) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.apiTSev l' d' recvTSRequestTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcNbl (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.apiTSev l' d' sendTSReplyTxIds) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.apiTSev l' d' sendTSReplyTxs) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.apiTSev l' d' sendTSDone) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.apiTSev l' d' sendTSRequestTxIdsBlocking) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.apiTSev l' d' sendTSRequestTxIdsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.apiTSev l' d' sendTSRequestTxsPipelined) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.apiTSev l' d' recvTSRequestTxIds) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.apiTSev l' d' recvTSRequestTxs) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTxs (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWri ids) (TS.sendTS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWri ids) (TS.sendTS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWri ids) (TS.sendTS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWri _) (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWri _) (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWri _) (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcWdone (TS.sendTS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcWdone (TS.sendTS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcWdone (TS.sendTS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcWdone (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcWdone (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcWdone (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWrt txs) (TS.sendTS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWrt txs) (TS.sendTS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWrt txs) (TS.sendTS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWrt _) (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWrt _) (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d (NS.tcWrt _) (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTerm (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTerm (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTerm (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsCnxt-io-role l d NS.tcTerm (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)

tsSnxt-io-role : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X} {q′ : NS.TSsPos}
  → NS.tsSnxt l d q (X , ιTS e₁) a ≡ just q′
  → (tsEvDir e₁ ≡ d) × ServerIo (ιTS e₁) a
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSInit} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSDone} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.receiveTS l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsInit (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.apiTSev l' d' sendTSReplyTxIds) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.apiTSev l' d' sendTSReplyTxs) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.apiTSev l' d' sendTSDone) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.apiTSev l' d' sendTSRequestTxIdsBlocking) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.apiTSev l' d' sendTSRequestTxIdsPipelined) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.apiTSev l' d' sendTSRequestTxsPipelined) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.apiTSev l' d' recvTSRequestTxIds) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.apiTSev l' d' recvTSRequestTxs) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsIdle (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWib (na , r)) (TS.sendTS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking na r))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWib (na , r)) (TS.sendTS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWib (na , r)) (TS.sendTS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWib _) (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWib _) (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWib _) (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWin (na , r)) (TS.sendTS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking na r))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWin (na , r)) (TS.sendTS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWin (na , r)) (TS.sendTS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWin _) (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWin _) (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWin _) (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWrt ids) (TS.sendTS l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWrt ids) (TS.sendTS l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWrt ids) (TS.sendTS l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWrt _) (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWrt _) (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d (NS.tsWrt _) (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSInit} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSDone} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.receiveTS l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsBlk (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSInit} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSDone} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.receiveTS l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsNbl (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSInit} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , txSubmission MsgTSDone} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.receiveTS l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTxs (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsDdone (TS.doneTS l' d') eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsDdone (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsDdone (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsDdone (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTerm (TS.sendTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTerm (TS.receiveTS l' d') eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTerm (TS.apiTSev l' d' m) eq = ⊥-elim (nothing-absurd eq)
tsSnxt-io-role l d NS.tsTerm (TS.doneTS l' d') eq = ⊥-elim (nothing-absurd eq)

absTSc-io : (l : Link) (d : Dir) (q : TScPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → absTSc l d q ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → (tsEvDir e₁ ≡ d) × ClientIo (ιTS e₁) a
absTSc-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d }) (coarsenTSc q) step
... | (q′ , nxtEq , _) = tsCnxt-io-role l d (coarsenTSc q) e₁ {a} nxtEq

absTSs-io : (l : Link) (d : Dir) (q : TSsPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → absTSs l d q ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → (tsEvDir e₁ ≡ d) × ServerIo (ιTS e₁) a
absTSs-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d }) (coarsenTSs q) step
... | (q′ , nxtEq , _) = tsSnxt-io-role l d (coarsenTSs q) e₁ {a} nxtEq

lnCnxt-io-role : (l : Link) (d : Dir) (q : NS.LNcPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X} {q′ : NS.LNcPos}
  → NS.lnCnxt l d q (X , ιLN e₁) a ≡ just q′
  → (lnEvDir e₁ ≡ d) × ClientIo (ιLN e₁) a
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' sendLNRequestNext) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' sendLNDone) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' sendLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' sendLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' sendLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' sendLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' recvLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' recvLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' recvLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.apiLNev l' d' recvLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncIdle (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWreq (LNp.sendLN l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWreq (LNp.sendLN l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWreq (LNp.sendLN l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWreq (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWreq (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWreq (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWdone (LNp.sendLN l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWdone (LNp.sendLN l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWdone (LNp.sendLN l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWdone (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWdone (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncWdone (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify MsgLNRequestNext} eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify MsgLNDone} eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.receiveLN l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncBusy (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' sendLNRequestNext) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' sendLNDone) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' sendLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' sendLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' sendLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' sendLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' recvLNBlockAnnouncement) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' recvLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' recvLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.apiLNev l' d' recvLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRann _) (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' sendLNRequestNext) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' sendLNDone) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' sendLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' sendLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' sendLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' sendLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' recvLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' recvLNBlockOffer) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' recvLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.apiLNev l' d' recvLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRoff _) (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' sendLNRequestNext) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' sendLNDone) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' sendLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' sendLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' sendLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' sendLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' recvLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' recvLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' recvLNBlockTxsOffer) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.apiLNev l' d' recvLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRtxs _) (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' sendLNRequestNext) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' sendLNDone) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' sendLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' sendLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' sendLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' sendLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' recvLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' recvLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' recvLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.apiLNev l' d' recvLNVotesOffer) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d (NS.lncRvot _) (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncTerm (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncTerm (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncTerm (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnCnxt-io-role l d NS.lncTerm (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)

lnSnxt-io-role : (l : Link) (d : Dir) (q : NS.LNsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X} {q′ : NS.LNsPos}
  → NS.lnSnxt l d q (X , ιLN e₁) a ≡ just q′
  → (lnEvDir e₁ ≡ d) × ServerIo (ιLN e₁) a
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify MsgLNRequestNext} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , leiosNotify MsgLNDone} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.receiveLN l' d') {a = _ , _ , _ , leiosFetch _} eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsIdle (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' sendLNRequestNext) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' sendLNDone) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' sendLNBlockAnnouncement) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' sendLNBlockOffer) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' sendLNBlockTxsOffer) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' sendLNVotesOffer) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' recvLNBlockAnnouncement) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' recvLNBlockOffer) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' recvLNBlockTxsOffer) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.apiLNev l' d' recvLNVotesOffer) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsBusy (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWann h) (LNp.sendLN l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWann h) (LNp.sendLN l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWann h) (LNp.sendLN l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWann _) (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWann _) (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWann _) (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWoff q) (LNp.sendLN l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWoff q) (LNp.sendLN l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWoff q) (LNp.sendLN l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWoff _) (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWoff _) (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWoff _) (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWtxs q) (LNp.sendLN l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWtxs q) (LNp.sendLN l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWtxs q) (LNp.sendLN l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWtxs _) (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWtxs _) (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWtxs _) (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWvot vs) (LNp.sendLN l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWvot vs) (LNp.sendLN l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWvot vs) (LNp.sendLN l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWvot _) (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWvot _) (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d (NS.lnsWvot _) (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsDone (LNp.doneLN l' d') eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsDone (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsDone (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsDone (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsTerm (LNp.sendLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsTerm (LNp.receiveLN l' d') eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsTerm (LNp.apiLNev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lnSnxt-io-role l d NS.lnsTerm (LNp.doneLN l' d') eq = ⊥-elim (nothing-absurd eq)

absLNc-io : (l : Link) (d : Dir) (q : LNcPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {M : NetProc}
  → absLNc l d q ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → (lnEvDir e₁ ≡ d) × ClientIo (ιLN e₁) a
absLNc-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d }) (coarsenLNc q) step
... | (q′ , nxtEq , _) = lnCnxt-io-role l d (coarsenLNc q) e₁ {a} nxtEq

absLNs-io : (l : Link) (d : Dir) (q : LNsPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {M : NetProc}
  → absLNs l d q ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → (lnEvDir e₁ ≡ d) × ServerIo (ιLN e₁) a
absLNs-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d }) (coarsenLNs q) step
... | (q′ , nxtEq , _) = lnSnxt-io-role l d (coarsenLNs q) e₁ {a} nxtEq

lfCnxt-io-role : (l : Link) (d : Dir) (q : NS.LFcPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X} {q′ : NS.LFcPos}
  → NS.lfCnxt l d q (X , ιLF e₁) a ≡ just q′
  → (lfEvDir e₁ ≡ d) × ClientIo (ιLF e₁) a
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFBlockRequest) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFVotesRequest) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFDone) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' recvLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' recvLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' recvLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.apiLFev l' d' recvLFRangeBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcIdle (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWblk pt) (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWblk pt) (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWblk pt) (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWblk _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWblk _) (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWblk _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWtxs (pt , bm)) (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWtxs (pt , bm)) (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWtxs (pt , bm)) (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWtxs _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWtxs _) (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWtxs _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWvot vs) (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWvot vs) (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWvot vs) (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWvot _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWvot _) (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWvot _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWrng r) (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWrng r) (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWrng r) (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWrng _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWrng _) (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcWrng _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcWdone (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone)
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcWdone (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcWdone (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcWdone (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcWdone (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcWdone (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch MsgLFDone} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.receiveLF l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBlk (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch MsgLFDone} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.receiveLF l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcBtx (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch MsgLFDone} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.receiveLF l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcVot (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch MsgLFDone} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.receiveLF l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcRng (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFBlockRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFVotesRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFDone) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' recvLFBlock) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' recvLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' recvLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.apiLFev l' d' recvLFRangeBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRblk _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFBlockRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFVotesRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFDone) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' recvLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' recvLFBlockTxs) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' recvLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.apiLFev l' d' recvLFRangeBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRbtx _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFBlockRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFVotesRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFDone) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' recvLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' recvLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' recvLFVoteDelivery) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.apiLFev l' d' recvLFRangeBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRvot _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFBlockRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFVotesRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFDone) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' recvLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' recvLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' recvLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.apiLFev l' d' recvLFRangeBlock) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRnextRng _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFBlockRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFVotesRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFDone) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' recvLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' recvLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' recvLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.apiLFev l' d' recvLFRangeBlock) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d (NS.lfcRlastRng _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcTerm (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcTerm (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcTerm (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfCnxt-io-role l d NS.lfcTerm (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)

lfSnxt-io-role : (l : Link) (d : Dir) (q : NS.LFsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X} {q′ : NS.LFsPos}
  → NS.lfSnxt l d q (X , ιLF e₁) a ≡ just q′
  → (lfEvDir e₁ ≡ d) × ServerIo (ιLF e₁) a
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch MsgLFDone} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , refl
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , chainSync _} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , blockFetch _} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , txSubmission _} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , keepAlive _} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.receiveLF l' d') {a = _ , _ , _ , leiosNotify _} eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsIdle (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFBlockRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFVotesRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFDone) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFBlock) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' recvLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' recvLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' recvLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.apiLFev l' d' recvLFRangeBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBlk (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFBlockRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFVotesRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFDone) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFBlockTxs) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' recvLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' recvLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' recvLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.apiLFev l' d' recvLFRangeBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsBtx (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFBlockRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFVotesRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFDone) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFVoteDelivery) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' recvLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' recvLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' recvLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.apiLFev l' d' recvLFRangeBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsVot (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFBlockRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFBlockTxsRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFVotesRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFBlockRangeRequest) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFDone) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange) eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' recvLFBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' recvLFBlockTxs) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' recvLFVoteDelivery) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.apiLFev l' d' recvLFRangeBlock) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsRng (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWblk b) (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWblk b) (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWblk b) (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWblk _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWblk _) (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWblk _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWtxs ts) (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWtxs ts) (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWtxs ts) (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWtxs _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWtxs _) (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWtxs _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWvot vs) (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWvot vs) (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWvot vs) (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWvot _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWvot _) (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWvot _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWnext (b , ts)) (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWnext (b , ts)) (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWnext (b , ts)) (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWnext _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWnext _) (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWnext _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWlast (b , ts)) (LFp.sendLF l' d') {a} eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts))
...   | yes refl = refl , refl
...   | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWlast (b , ts)) (LFp.sendLF l' d') eq | yes refl | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWlast (b , ts)) (LFp.sendLF l' d') eq | no _ | _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWlast _) (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWlast _) (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d (NS.lfsWlast _) (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsDone (LFp.doneLF l' d') eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = refl , tt
... | yes refl | no _ = ⊥-elim (nothing-absurd eq)
... | no _ | yes refl = ⊥-elim (nothing-absurd eq)
... | no _ | no _ = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsDone (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsDone (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsDone (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsTerm (LFp.sendLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsTerm (LFp.receiveLF l' d') eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsTerm (LFp.apiLFev l' d' m) eq = ⊥-elim (nothing-absurd eq)
lfSnxt-io-role l d NS.lfsTerm (LFp.doneLF l' d') eq = ⊥-elim (nothing-absurd eq)

absLFc-io : (l : Link) (d : Dir) (q : LFcPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {M : NetProc}
  → absLFc l d q ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → (lfEvDir e₁ ≡ d) × ClientIo (ιLF e₁) a
absLFc-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d }) (coarsenLFc q) step
... | (q′ , nxtEq , _) = lfCnxt-io-role l d (coarsenLFc q) e₁ {a} nxtEq

absLFs-io : (l : Link) (d : Dir) (q : LFsPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {M : NetProc}
  → absLFs l d q ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → (lfEvDir e₁ ≡ d) × ServerIo (ιLF e₁) a
absLFs-io l d q {X} {e₁} {a} step
  with tableSpec-ev-inv (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d }) (coarsenLFs q) step
... | (q′ , nxtEq , _) = lfSnxt-io-role l d (coarsenLFs q) e₁ {a} nxtEq



------------------------------------------------------------------------
-- ITEM-3b-ABSTRACT (rest) — CS/BF/TS/LN/LF abstract bundle io-role peels +
-- absBundleG-io-role dispatcher (mirror concrete SysIoLink2 bundleG-io-role).
------------------------------------------------------------------------

-- absBundleCS-io-role : role fingerprint of a CS-image abstract bundle io step
absBundleCS-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► Bd′
  → (dirOf (ιCS e₁) ≡ cl × ClientIo (ιCS e₁) a) ⊎ (dirOf (ιCS e₁) ≡ sv × ServerIo (ιCS e₁) a)
absBundleCS-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = ⊥-elim (absKAc-noCS l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noCS l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = ⊥-elim (absKAs-noCS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noCS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = inj₁ (mkInjC ιCS csEvDir csDirOf-ι (e₁ , refl , proj₁ (absCSc-io l cl csc sM) , proj₂ (absCSc-io l cl csc sM)))
...     | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absCSs l sv css) _ (absCSs-dir-noBoth l sv css e₁ (λ q → cl≢sv (trans (sym (proj₁ (absCSc-io l cl csc sM))) q))) (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noCS l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noCS l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁)))))))) (_ , sTail))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = inj₂ (mkInjS ιCS csEvDir csDirOf-ι (e₁ , refl , proj₁ (absCSs-io l sv css sM) , proj₂ (absCSs-io l sv css sM)))
...       | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noCS l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noCS l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁))))))) (_ , sTail))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = ⊥-elim (absBFc-noCS l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noCS l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = ⊥-elim (absBFs-noCS l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noCS l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = ⊥-elim (absTSc-noCS l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noCS l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = ⊥-elim (absTSs-noCS l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noCS l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = ⊥-elim (absLNc-noCS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noCS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = ⊥-elim (absLNs-noCS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noCS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = ⊥-elim (absLFc-noCS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noCS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs = ⊥-elim (absLFs-noCS l sv (lfs ip) e₁ (_ , qs))

-- absBundleBF-io-role : role fingerprint of a BF-image abstract bundle io step
absBundleBF-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → (dirOf (ιBF e₁) ≡ cl × ClientIo (ιBF e₁) a) ⊎ (dirOf (ιBF e₁) ≡ sv × ServerIo (ιBF e₁) a)
absBundleBF-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = ⊥-elim (absKAc-noBF l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noBF l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = ⊥-elim (absKAs-noBF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noBF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = ⊥-elim (absCSc-noBF l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noBF l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = ⊥-elim (absCSs-noBF l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noBF l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = inj₁ (mkInjC ιBF bfEvDir bfDirOf-ι (e₁ , refl , proj₁ (absBFc-io l cl bfc sM) , proj₂ (absBFc-io l cl bfc sM)))
...         | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-dir-noBoth l sv bfs e₁ (λ q → cl≢sv (trans (sym (proj₁ (absBFc-io l cl bfc sM))) q))) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁)))))) (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = inj₂ (mkInjS ιBF bfEvDir bfDirOf-ι (e₁ , refl , proj₁ (absBFs-io l sv bfs sM) , proj₂ (absBFs-io l sv bfs sM)))
...           | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁))))) (_ , sTail))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = ⊥-elim (absTSc-noBF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noBF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = ⊥-elim (absTSs-noBF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noBF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = ⊥-elim (absLNc-noBF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noBF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = ⊥-elim (absLNs-noBF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noBF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = ⊥-elim (absLFc-noBF l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noBF l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs = ⊥-elim (absLFs-noBF l sv (lfs ip) e₁ (_ , qs))

-- absBundleTS-io-role : role fingerprint of a TS-image abstract bundle io step
absBundleTS-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► Bd′
  → (dirOf (ιTS e₁) ≡ cl × ClientIo (ιTS e₁) a) ⊎ (dirOf (ιTS e₁) ≡ sv × ServerIo (ιTS e₁) a)
absBundleTS-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = ⊥-elim (absKAc-noTS l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noTS l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = ⊥-elim (absKAs-noTS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noTS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = ⊥-elim (absCSc-noTS l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noTS l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = ⊥-elim (absCSs-noTS l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noTS l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = ⊥-elim (absBFc-noTS l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noTS l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = ⊥-elim (absBFs-noTS l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noTS l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = inj₁ (mkInjC ιTS tsEvDir tsDirOf-ι (e₁ , refl , proj₁ (absTSc-io l cl (tsc ip) sM) , proj₂ (absTSc-io l cl (tsc ip) sM)))
...             | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-dir-noBoth l sv (tss ip) e₁ (λ q → cl≢sv (trans (sym (proj₁ (absTSc-io l cl (tsc ip) sM))) q))) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noTS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noTS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noTS l cl (lfc ip) e₁) (absLFs-noTS l sv (lfs ip) e₁)))) (_ , sTail))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = inj₂ (mkInjS ιTS tsEvDir tsDirOf-ι (e₁ , refl , proj₁ (absTSs-io l sv (tss ip) sM) , proj₂ (absTSs-io l sv (tss ip) sM)))
...               | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noTS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noTS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noTS l cl (lfc ip) e₁) (absLFs-noTS l sv (lfs ip) e₁))) (_ , sTail))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = ⊥-elim (absLNc-noTS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noTS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = ⊥-elim (absLNs-noTS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noTS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = ⊥-elim (absLFc-noTS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noTS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs = ⊥-elim (absLFs-noTS l sv (lfs ip) e₁ (_ , qs))

-- absBundleLN-io-role : role fingerprint of a LN-image abstract bundle io step
absBundleLN-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► Bd′
  → (dirOf (ιLN e₁) ≡ cl × ClientIo (ιLN e₁) a) ⊎ (dirOf (ιLN e₁) ≡ sv × ServerIo (ιLN e₁) a)
absBundleLN-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = ⊥-elim (absKAc-noLN l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noLN l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = ⊥-elim (absKAs-noLN l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noLN l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = ⊥-elim (absCSc-noLN l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noLN l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = ⊥-elim (absCSs-noLN l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noLN l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = ⊥-elim (absBFc-noLN l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noLN l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = ⊥-elim (absBFs-noLN l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noLN l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = ⊥-elim (absTSc-noLN l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noLN l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = ⊥-elim (absTSs-noLN l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noLN l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = inj₁ (mkInjC ιLN lnEvDir lnDirOf-ι (e₁ , refl , proj₁ (absLNc-io l cl (lnc ip) sM) , proj₂ (absLNc-io l cl (lnc ip) sM)))
...                 | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-dir-noBoth l sv (lns ip) e₁ (λ q → cl≢sv (trans (sym (proj₁ (absLNc-io l cl (lnc ip) sM))) q))) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noLN l cl (lfc ip) e₁) (absLFs-noLN l sv (lfs ip) e₁)) (_ , sTail))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = inj₂ (mkInjS ιLN lnEvDir lnDirOf-ι (e₁ , refl , proj₁ (absLNs-io l sv (lns ip) sM) , proj₂ (absLNs-io l sv (lns ip) sM)))
...                   | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noLN l cl (lfc ip) e₁) (absLFs-noLN l sv (lfs ip) e₁) (_ , sTail))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = ⊥-elim (absLFc-noLN l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noLN l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs = ⊥-elim (absLFs-noLN l sv (lfs ip) e₁ (_ , qs))

-- absBundleLF-io-role : role fingerprint of a LF-image abstract bundle io step
absBundleLF-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► Bd′
  → (dirOf (ιLF e₁) ≡ cl × ClientIo (ιLF e₁) a) ⊎ (dirOf (ιLF e₁) ≡ sv × ServerIo (ιLF e₁) a)
absBundleLF-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = ⊥-elim (absKAc-noLF l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noLF l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = ⊥-elim (absKAs-noLF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noLF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = ⊥-elim (absCSc-noLF l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noLF l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = ⊥-elim (absCSs-noLF l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noLF l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = ⊥-elim (absBFc-noLF l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noLF l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = ⊥-elim (absBFs-noLF l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noLF l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = ⊥-elim (absTSc-noLF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noLF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = ⊥-elim (absTSs-noLF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noLF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = ⊥-elim (absLNc-noLF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noLF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = ⊥-elim (absLNs-noLF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noLF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = inj₁ (mkInjC ιLF lfEvDir lfDirOf-ι (e₁ , refl , proj₁ (absLFc-io l cl (lfc ip) sM) , proj₂ (absLFc-io l cl (lfc ip) sM)))
...                     | PEA.evBoth _ sM sTail = ⊥-elim (absLFs-dir-noBoth l sv (lfs ip) e₁ (λ q → cl≢sv (trans (sym (proj₁ (absLFc-io l cl (lfc ip) sM))) q)) (_ , sTail))
...                     | PEA.evR _ qs = inj₂ (mkInjS ιLF lfEvDir lfDirOf-ι (e₁ , refl , proj₁ (absLFs-io l sv (lfs ip) qs) , proj₂ (absLFs-io l sv (lfs ip) qs)))


-- absBundleG-io-role : abstract bundle dispatcher over the raw io event e
absBundleG-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → (dirOf e ≡ cl × ClientIo e a) ⊎ (dirOf e ≡ sv × ServerIo e a)
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_ChainSync}   iomem step = absBundleCS-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.sendCS    l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_ChainSync}   iomem step = absBundleCS-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.receiveCS l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_BlockFetch}  iomem step = absBundleBF-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.sendBF    l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_BlockFetch}  iomem step = absBundleBF-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.receiveBF l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_KeepAlive}   iomem step = absBundleKA-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.sendKA    l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_KeepAlive}   iomem step = absBundleKA-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.receiveKA l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_TxSubmission} iomem step = absBundleTS-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.sendTS    l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_TxSubmission} iomem step = absBundleTS-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.receiveTS l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosNotify} iomem step = absBundleLN-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.sendLN   l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosNotify} iomem step = absBundleLN-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.receiveLN l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosFetch}  iomem step = absBundleLF-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.sendLF   l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosFetch}  iomem step = absBundleLF-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.receiveLF l′ d′} step
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = done   _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiCS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiBF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiKA  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiTS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiLN  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiLF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- ITEM-3c-ABSTRACT — abstract io node disjointness: absBundleG-io-ahl +
-- absNodeX-io-fp x4 + pairwise absNodeY-io-no-when-X x6 + absGroupA/B-io-no
-- (byte-transform of concrete SysIoLink2 item-3c; drivers/RoleFP/role-clash/
-- lo≢hi/apiLink-inj/link-diseqs reused; bundleG→absBundleG).
------------------------------------------------------------------------

-- absBundleG-io-ahl : the abstract bundle link fingerprint (mirror concrete
-- bundleG-io-ahl); derived WITHOUT new peels — decide l′ ≟ l, else the
-- wrong-link non-offer `absBundleG-io-no` refutes the actual firing step.
absBundleG-io-ahl : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → ApiHasLink l e
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_ChainSync} iomem step with l′ ≟ l
... | yes refl = ahlIn
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlIn l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_BlockFetch} iomem step with l′ ≟ l
... | yes refl = ahlIn
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlIn l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_KeepAlive} iomem step with l′ ≟ l
... | yes refl = ahlIn
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlIn l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_TxSubmission} iomem step with l′ ≟ l
... | yes refl = ahlIn
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlIn l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosNotify} iomem step with l′ ≟ l
... | yes refl = ahlIn
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlIn l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosFetch} iomem step with l′ ≟ l
... | yes refl = ahlIn
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlIn l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output  l′ d′ N2N_ChainSync} iomem step with l′ ≟ l
... | yes refl = ahlOut
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlOut l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output  l′ d′ N2N_BlockFetch} iomem step with l′ ≟ l
... | yes refl = ahlOut
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlOut l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output  l′ d′ N2N_KeepAlive} iomem step with l′ ≟ l
... | yes refl = ahlOut
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlOut l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output  l′ d′ N2N_TxSubmission} iomem step with l′ ≟ l
... | yes refl = ahlOut
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlOut l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output  l′ d′ N2N_LeiosNotify} iomem step with l′ ≟ l
... | yes refl = ahlOut
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlOut l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = output  l′ d′ N2N_LeiosFetch} iomem step with l′ ≟ l
... | yes refl = ahlOut
... | no l′≢l = ⊥-elim (absBundleG-io-no l cl sv csc css bfc bfs ip ahlOut l′≢l iomem (_ , step))
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = done   _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiCS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiBF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiKA  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiTS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiLN  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = apiLF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-ahl l cl sv cl≢sv csc css bfc bfs ip {e = break  _} iomem step = ⊥-elim iomem

-- the four node io fingerprints (link + per-link (dir,role))
-- node-A io fingerprint: link + (dir,role) read off the firing bundle
absNodeA-io-fp : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → ioES .mem (X , e) a
  → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
absNodeA-io-fp na {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (decProd linkAB hi b1 (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi b1 (SN.NodeStateA.prod-AC na))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeA-drv-io-no na iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeA-drv-io-no na iomem (_ , sD))
... | PEA.evL _ sB
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
           (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
           sB
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
          (apiLink-inj (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
                       (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)))
...   | PEA.evL _ sBAB = inj₁ (absBundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB , absBundleG-io-role linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
...   | PEA.evR _ sBAC = inj₂ (absBundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC , absBundleG-io-role linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)

-- node-B io fingerprint: link + (dir,role) read off the firing bundle
absNodeB-io-fp : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B′ : NetProc}
  → ioES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► B′
  → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
absNodeB-io-fp nb {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeB-drv-io-no nb iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeB-drv-io-no nb iomem (_ , sD))
... | PEA.evL _ sBb
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
           sBb
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sBAB sBBD = ⊥-elim (linkAB≢linkBD
          (apiLink-inj (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
                       (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)))
...   | PEA.evL _ sBAB = inj₁ (absBundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB , absBundleG-io-role linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
...   | PEA.evR _ sBBD = inj₂ (absBundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD , absBundleG-io-role linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)

-- node-C io fingerprint: link + (dir,role) read off the firing bundle
absNodeC-io-fp : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {C′ : NetProc}
  → ioES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► C′
  → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
absNodeC-io-fp nc {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sD      = ⊥-elim (nodeC-drv-io-no nc iomem (_ , sD))
... | PEA.evBoth _ _ sD = ⊥-elim (nodeC-drv-io-no nc iomem (_ , sD))
... | PEA.evL _ sCc
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
           sCc
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sCAC sCCD = ⊥-elim (linkAC≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sCAC)
                       (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sCCD)))
...   | PEA.evL _ sCAC = inj₁ (absBundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sCAC , absBundleG-io-role linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sCAC)
...   | PEA.evR _ sCCD = inj₂ (absBundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sCCD , absBundleG-io-role linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sCCD)

-- node-D io fingerprint: link + (dir,role) read off the firing bundle
absNodeD-io-fp : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {D′ : NetProc}
  → ioES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► D′
  → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
absNodeD-io-fp nd {X} {e} {a} iomem step
  with PEA.Par-ev-elim apiES (λ _ _ → tt)
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd))
         step
... | PEA.evSync amem _ _ = ⊥-elim (io⇒¬api {X} {e} {a} iomem amem)
... | PEA.evR _ sDr      = ⊥-elim (nodeD-drv-io-no nd iomem (_ , sDr))
... | PEA.evBoth _ _ sDr = ⊥-elim (nodeD-drv-io-no nd iomem (_ , sDr))
... | PEA.evL _ sDd
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
           sDd
...   | PEA.evSync () _ _
...   | PEA.evBoth _ sDBD sDCD = ⊥-elim (linkBD≢linkCD
          (apiLink-inj (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sDBD)
                       (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sDCD)))
...   | PEA.evL _ sDBD = inj₁ (absBundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sDBD , absBundleG-io-role linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sDBD)
...   | PEA.evR _ sDCD = inj₂ (absBundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sDCD , absBundleG-io-role linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sDCD)

------------------------------------------------------------------------
-- pairwise sibling non-offers (io): a node cannot offer an event fired by
-- another node, given the firing node's io fingerprint.
------------------------------------------------------------------------

-- node B when A fires (shared link AB)
absNodeB-io-no-when-A : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
  → ¬ IoOffers (absNodeB nb) e a
absNodeB-io-no-when-A nb iomem fpA (M , step) with absNodeB-io-fp nb iomem step | fpA
... | inj₁ (ahlB , roleB) | inj₁ (ahlA , roleA) = role-clash lo hi lo≢hi iomem roleA roleB
... | inj₁ (ahlB , _)     | inj₂ (ahlA , _)     = linkAB≢linkAC (apiLink-inj ahlB ahlA)
... | inj₂ (ahlB , _)     | inj₁ (ahlA , _)     = linkAB≢linkBD (apiLink-inj ahlA ahlB)
... | inj₂ (ahlB , _)     | inj₂ (ahlA , _)     = linkAC≢linkBD (apiLink-inj ahlA ahlB)

-- node C when A fires (shared link AC)
absNodeC-io-no-when-A : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
  → ¬ IoOffers (absNodeC nc) e a
absNodeC-io-no-when-A nc iomem fpA (M , step) with absNodeC-io-fp nc iomem step | fpA
... | inj₁ (ahlC , roleC) | inj₂ (ahlA , roleA) = role-clash lo hi lo≢hi iomem roleA roleC
... | inj₁ (ahlC , _)     | inj₁ (ahlA , _)     = linkAB≢linkAC (apiLink-inj ahlA ahlC)
... | inj₂ (ahlC , _)     | inj₁ (ahlA , _)     = linkAB≢linkCD (apiLink-inj ahlA ahlC)
... | inj₂ (ahlC , _)     | inj₂ (ahlA , _)     = linkAC≢linkCD (apiLink-inj ahlA ahlC)

-- node D when A fires (no shared link)
absNodeD-io-no-when-A : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
  → ¬ IoOffers (absNodeD nd) e a
absNodeD-io-no-when-A nd iomem fpA (M , step) with absNodeD-io-fp nd iomem step | fpA
... | inj₁ (ahlD , _) | inj₁ (ahlA , _) = linkAB≢linkBD (apiLink-inj ahlA ahlD)
... | inj₁ (ahlD , _) | inj₂ (ahlA , _) = linkAC≢linkBD (apiLink-inj ahlA ahlD)
... | inj₂ (ahlD , _) | inj₁ (ahlA , _) = linkAB≢linkCD (apiLink-inj ahlA ahlD)
... | inj₂ (ahlD , _) | inj₂ (ahlA , _) = linkAC≢linkCD (apiLink-inj ahlA ahlD)

-- node C when B fires (no shared link)
absNodeC-io-no-when-B : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
  → ¬ IoOffers (absNodeC nc) e a
absNodeC-io-no-when-B nc iomem fpB (M , step) with absNodeC-io-fp nc iomem step | fpB
... | inj₁ (ahlC , _) | inj₁ (ahlB , _) = linkAB≢linkAC (apiLink-inj ahlB ahlC)
... | inj₁ (ahlC , _) | inj₂ (ahlB , _) = linkAC≢linkBD (apiLink-inj ahlC ahlB)
... | inj₂ (ahlC , _) | inj₁ (ahlB , _) = linkAB≢linkCD (apiLink-inj ahlB ahlC)
... | inj₂ (ahlC , _) | inj₂ (ahlB , _) = linkBD≢linkCD (apiLink-inj ahlB ahlC)

-- node D when B fires (shared link BD)
absNodeD-io-no-when-B : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
  → ¬ IoOffers (absNodeD nd) e a
absNodeD-io-no-when-B nd iomem fpB (M , step) with absNodeD-io-fp nd iomem step | fpB
... | inj₁ (ahlD , roleD) | inj₂ (ahlB , roleB) = role-clash lo hi lo≢hi iomem roleB roleD
... | inj₁ (ahlD , _)     | inj₁ (ahlB , _)     = linkAB≢linkBD (apiLink-inj ahlB ahlD)
... | inj₂ (ahlD , _)     | inj₁ (ahlB , _)     = linkAB≢linkCD (apiLink-inj ahlB ahlD)
... | inj₂ (ahlD , _)     | inj₂ (ahlB , _)     = linkBD≢linkCD (apiLink-inj ahlB ahlD)

-- node D when C fires (shared link CD)
absNodeD-io-no-when-C : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
  → ¬ IoOffers (absNodeD nd) e a
absNodeD-io-no-when-C nd iomem fpC (M , step) with absNodeD-io-fp nd iomem step | fpC
... | inj₂ (ahlD , roleD) | inj₂ (ahlC , roleC) = role-clash lo hi lo≢hi iomem roleC roleD
... | inj₁ (ahlD , _)     | inj₁ (ahlC , _)     = linkAC≢linkBD (apiLink-inj ahlC ahlD)
... | inj₁ (ahlD , _)     | inj₂ (ahlC , _)     = linkBD≢linkCD (apiLink-inj ahlD ahlC)
... | inj₂ (ahlD , _)     | inj₁ (ahlC , _)     = linkAC≢linkCD (apiLink-inj ahlC ahlD)

------------------------------------------------------------------------
-- group non-offers (io): the sibling group of a firing node offers nothing
------------------------------------------------------------------------
absGroupA-io-no : (na : SN.NodeStateA) (nb : SN.NodeStateB) (nc : SN.NodeStateC) (nd : SN.NodeStateD)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → ioES .mem (X , e) a → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → ¬ IoOffers (absNodeB nb ⦀ (absNodeC nc ⦀ absNodeD nd)) e a
absGroupA-io-no na nb nc nd iomem sA =
  SStep.⦀-noOffer (absNodeB nb) (absNodeC nc ⦀ absNodeD nd)
    (absNodeB-io-no-when-A nb iomem fpA)
    (SStep.⦀-noOffer (absNodeC nc) (absNodeD nd) (absNodeC-io-no-when-A nc iomem fpA) (absNodeD-io-no-when-A nd iomem fpA))
  where fpA = absNodeA-io-fp na iomem sA

absGroupB-io-no : (nb : SN.NodeStateB) (nc : SN.NodeStateC) (nd : SN.NodeStateD)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B′ : NetProc}
  → ioES .mem (X , e) a → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► B′
  → ¬ IoOffers (absNodeC nc ⦀ absNodeD nd) e a
absGroupB-io-no nb nc nd iomem sB =
  SStep.⦀-noOffer (absNodeC nc) (absNodeD nd) (absNodeC-io-no-when-B nc iomem fpB) (absNodeD-io-no-when-B nd iomem fpB)
  where fpB = absNodeB-io-fp nb iomem sB

------------------------------------------------------------------------
-- reverse-direction pairwise io non-offers (earlier node idle when a LATER
-- node fires) — the outer `⦀-ev-R` idle-sibling refutations `top-nodes-io`'s
-- abstract lift needs (mirror of the forward pairwise, columns swapped).
------------------------------------------------------------------------

-- node A when B fires (shared link AB)
absNodeA-io-no-when-B : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
  → ¬ IoOffers (absNodeA na) e a
absNodeA-io-no-when-B na iomem fpB (M , step) with absNodeA-io-fp na iomem step | fpB
... | inj₁ (ahlA , roleA) | inj₁ (ahlB , roleB) = role-clash lo hi lo≢hi iomem roleA roleB
... | inj₁ (ahlA , _)     | inj₂ (ahlB , _)     = linkAB≢linkBD (apiLink-inj ahlA ahlB)
... | inj₂ (ahlA , _)     | inj₁ (ahlB , _)     = linkAB≢linkAC (apiLink-inj ahlB ahlA)
... | inj₂ (ahlA , _)     | inj₂ (ahlB , _)     = linkAC≢linkBD (apiLink-inj ahlA ahlB)

-- node A when C fires (shared link AC)
absNodeA-io-no-when-C : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
  → ¬ IoOffers (absNodeA na) e a
absNodeA-io-no-when-C na iomem fpC (M , step) with absNodeA-io-fp na iomem step | fpC
... | inj₂ (ahlA , roleA) | inj₁ (ahlC , roleC) = role-clash lo hi lo≢hi iomem roleA roleC
... | inj₁ (ahlA , _)     | inj₁ (ahlC , _)     = linkAB≢linkAC (apiLink-inj ahlA ahlC)
... | inj₁ (ahlA , _)     | inj₂ (ahlC , _)     = linkAB≢linkCD (apiLink-inj ahlA ahlC)
... | inj₂ (ahlA , _)     | inj₂ (ahlC , _)     = linkAC≢linkCD (apiLink-inj ahlA ahlC)

-- node B when C fires (no shared link)
absNodeB-io-no-when-C : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
  → ¬ IoOffers (absNodeB nb) e a
absNodeB-io-no-when-C nb iomem fpC (M , step) with absNodeB-io-fp nb iomem step | fpC
... | inj₁ (ahlB , _) | inj₁ (ahlC , _) = linkAB≢linkAC (apiLink-inj ahlB ahlC)
... | inj₁ (ahlB , _) | inj₂ (ahlC , _) = linkAB≢linkCD (apiLink-inj ahlB ahlC)
... | inj₂ (ahlB , _) | inj₁ (ahlC , _) = linkAC≢linkBD (apiLink-inj ahlC ahlB)
... | inj₂ (ahlB , _) | inj₂ (ahlC , _) = linkBD≢linkCD (apiLink-inj ahlB ahlC)

-- node A when D fires (no shared link)
absNodeA-io-no-when-D : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
  → ¬ IoOffers (absNodeA na) e a
absNodeA-io-no-when-D na iomem fpD (M , step) with absNodeA-io-fp na iomem step | fpD
... | inj₁ (ahlA , _) | inj₁ (ahlD , _) = linkAB≢linkBD (apiLink-inj ahlA ahlD)
... | inj₁ (ahlA , _) | inj₂ (ahlD , _) = linkAB≢linkCD (apiLink-inj ahlA ahlD)
... | inj₂ (ahlA , _) | inj₁ (ahlD , _) = linkAC≢linkBD (apiLink-inj ahlA ahlD)
... | inj₂ (ahlA , _) | inj₂ (ahlD , _) = linkAC≢linkCD (apiLink-inj ahlA ahlD)

-- node B when D fires (shared link BD)
absNodeB-io-no-when-D : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
  → ¬ IoOffers (absNodeB nb) e a
absNodeB-io-no-when-D nb iomem fpD (M , step) with absNodeB-io-fp nb iomem step | fpD
... | inj₂ (ahlB , roleB) | inj₁ (ahlD , roleD) = role-clash lo hi lo≢hi iomem roleB roleD
... | inj₁ (ahlB , _)     | inj₁ (ahlD , _)     = linkAB≢linkBD (apiLink-inj ahlB ahlD)
... | inj₁ (ahlB , _)     | inj₂ (ahlD , _)     = linkAB≢linkCD (apiLink-inj ahlB ahlD)
... | inj₂ (ahlB , _)     | inj₂ (ahlD , _)     = linkBD≢linkCD (apiLink-inj ahlB ahlD)

-- node C when D fires (shared link CD)
absNodeC-io-no-when-D : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
  → ¬ IoOffers (absNodeC nc) e a
absNodeC-io-no-when-D nc iomem fpD (M , step) with absNodeC-io-fp nc iomem step | fpD
... | inj₂ (ahlC , roleC) | inj₂ (ahlD , roleD) = role-clash lo hi lo≢hi iomem roleC roleD
... | inj₁ (ahlC , _)     | inj₁ (ahlD , _)     = linkAC≢linkBD (apiLink-inj ahlC ahlD)
... | inj₂ (ahlC , _)     | inj₁ (ahlD , _)     = linkBD≢linkCD (apiLink-inj ahlD ahlC)
... | inj₁ (ahlC , _)     | inj₂ (ahlD , _)     = linkAC≢linkCD (apiLink-inj ahlC ahlD)

------------------------------------------------------------------------
-- ITEM 4 — `top-nodes-io`: the io analog of `top-nodes` (SysRoute:2158).
-- A hidden-io visible event of the 4-node `⦀` bundle (`nodesOf s`) is peeled to
-- a UNIQUE firing node: the interleave `evBoth` overlap is refuted by the io
-- group non-offers (`groupA/B-io-no`, `nodeD-io-no-when-C`), which pin the
-- firing node by link + (dir⊕role) — NO surviving evBoth (route (a), no
-- reachability).  The firing node is inverted by the DONE `nodeX-ev-io`
-- (returning `NodeXEvR`: successor `nx′`, `refl`, and the abstract firing step
-- `absNodeX (nX s) ─►absNodeX nx′`); `s′` is that single field update, so
-- `N₁ ≡ nodesOf s′` and `med s ≡ med s′` are `refl`.  The ABSTRACT nodes step is
-- lifted up `absNodesOf` by `⦀-ev-L/R` with idle siblings via the abstract
-- pairwise io non-offers (`absNodeY-io-no-when-X`).  Feeds `comove-io-sync`'s
-- `nodesEv` (concrete) and `absNodesEv` (abstract) on the SAME `s′`.
------------------------------------------------------------------------
top-nodes-io : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {N₁ : NetProc}
  → ioES .mem (X , e) a
  → SStep.nodesOf s ─[ ev (evl (evLabel X e a)) ]─► N₁
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (N₁ ≡ SStep.nodesOf s′) × (SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► SStep.absNodesOf s′)
top-nodes-io s iomem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (groupA-io-no (nA s) (nB s) (nC s) (nD s) iomem sA (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-io (nA s) iomem sA
...   | naEv na′ refl absStepA =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl , refl ,
        SStep.⦀-ev-L (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))
          absStepA
          (noOffer→viewV _ (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
             (absNodeB-io-no-when-A (nB s) iomem fpA)
             (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
                (absNodeC-io-no-when-A (nC s) iomem fpA) (absNodeD-io-no-when-A (nD s) iomem fpA))))
  where fpA = absNodeA-io-fp (nA s) iomem absStepA
top-nodes-io s iomem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (groupB-io-no (nB s) (nC s) (nD s) iomem sB (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-io (nB s) iomem sB
...   | nbIo nb′ refl absStepB =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl , refl ,
        SStep.⦀-ev-R (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))
          (SStep.⦀-ev-L (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
             absStepB
             (noOffer→viewV _ (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
                (absNodeC-io-no-when-B (nC s) iomem fpB) (absNodeD-io-no-when-B (nD s) iomem fpB))))
          (noOffer→viewV _ (absNodeA-io-no-when-B (nA s) iomem fpB))
  where fpB = absNodeB-io-fp (nB s) iomem absStepB
top-nodes-io s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (SN.decNodeC (nC s)) (SN.decNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (nodeD-io-no-when-C (nD s) iomem (nodeC-io-fp (nC s) iomem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-io (nC s) iomem sC
...   | ncIo nc′ refl absStepC =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl , refl ,
        SStep.⦀-ev-R (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))
          (SStep.⦀-ev-R (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
             (SStep.⦀-ev-L (absNodeC (nC s)) (absNodeD (nD s))
                absStepC
                (noOffer→viewV _ (absNodeD-io-no-when-C (nD s) iomem fpC)))
             (noOffer→viewV _ (absNodeB-io-no-when-C (nB s) iomem fpC)))
          (noOffer→viewV _ (absNodeA-io-no-when-C (nA s) iomem fpC))
  where fpC = absNodeC-io-fp (nC s) iomem absStepC
top-nodes-io s iomem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-io (nD s) iomem sD
... | ndIo nd′ refl absStepD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl , refl ,
        SStep.⦀-ev-R (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))
          (SStep.⦀-ev-R (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
             (SStep.⦀-ev-R (absNodeC (nC s)) (absNodeD (nD s))
                absStepD
                (noOffer→viewV _ (absNodeC-io-no-when-D (nC s) iomem fpD)))
             (noOffer→viewV _ (absNodeB-io-no-when-D (nB s) iomem fpD)))
          (noOffer→viewV _ (absNodeA-io-no-when-D (nA s) iomem fpD))
  where fpD = absNodeD-io-fp (nD s) iomem absStepD

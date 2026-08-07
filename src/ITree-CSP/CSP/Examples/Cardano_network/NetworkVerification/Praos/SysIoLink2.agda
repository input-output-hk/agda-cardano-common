{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 — io-peel layer, PART 2 (RAM split of SysIoLink).
-- Imports the cached `SysIoLink` interface publicly (cheap deserialise) plus
-- replicates its machinery import preamble, then carries all NEW io work from
-- item 3b-part2 onward: the value-role bundle assembly `bundleG-io-role`, the
-- node io-fingerprints, and `top-nodes-io`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink2 (blkA : Block₃) where


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

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink blkA public
-- ιKA/ιTS/ιLN come via SysIoLink's body-level NetworkPar import (not its
-- preamble), so re-import them here for the KA/TS/LN ι-bridges
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιKA; ιTS; ιLN )

------------------------------------------------------------------------
-- ITEM 3b-part2 support — direction projector + per-protocol ι-bridges + the
-- two role-injection assemblers.
------------------------------------------------------------------------

-- direction component of a Net_Api event (io + api all carry `(l , d , …)`)
dirOf : {X : Set 0ℓ} → Net_Api Payload X → Dir
dirOf (input  _ d _) = d
dirOf (output _ d _) = d
dirOf (done   _ d _) = d
dirOf (apiCS  _ d _) = d
dirOf (apiBF  _ d _) = d
dirOf (apiKA  _ d _) = d
dirOf (apiTS  _ d _) = d
dirOf (apiLN  _ d _) = d
dirOf (apiLF  _ d _) = d
dirOf (sndmsg _ d _) = d
dirOf (rcvmsg _ d _) = d
dirOf (tx     _ d _) = d
dirOf (sndack _ d _) = d
dirOf (rcvack _ d _) = d
dirOf (ack    _ d _) = d
dirOf (break  _)     = lo

-- ι-bridges: `dirOf` of a renamed source event equals that event's own dir
csDirOf-ι : {X : Set 0ℓ} (e₁ : CS.CSEv X) → dirOf (ιCS e₁) ≡ csEvDir e₁
csDirOf-ι (CS.sendCS _ _)    = refl
csDirOf-ι (CS.receiveCS _ _) = refl
csDirOf-ι (CS.apiCSev _ _ _) = refl
csDirOf-ι (CS.doneCS _ _)    = refl

bfDirOf-ι : {X : Set 0ℓ} (e₁ : BF.BFEv X) → dirOf (ιBF e₁) ≡ bfEvDir e₁
bfDirOf-ι (BF.sendBF _ _)    = refl
bfDirOf-ι (BF.receiveBF _ _) = refl
bfDirOf-ι (BF.apiBFev _ _ _) = refl
bfDirOf-ι (BF.doneBF _ _)    = refl

kaDirOf-ι : {X : Set 0ℓ} (e₁ : KA.KAEv X) → dirOf (ιKA e₁) ≡ kaEvDir e₁
kaDirOf-ι (KA.sendKA _ _)    = refl
kaDirOf-ι (KA.receiveKA _ _) = refl
kaDirOf-ι (KA.apiKAev _ _ _) = refl
kaDirOf-ι (KA.doneKA _ _)    = refl

tsDirOf-ι : {X : Set 0ℓ} (e₁ : TS.TSEv X) → dirOf (ιTS e₁) ≡ tsEvDir e₁
tsDirOf-ι (TS.sendTS _ _)    = refl
tsDirOf-ι (TS.receiveTS _ _) = refl
tsDirOf-ι (TS.apiTSev _ _ _) = refl
tsDirOf-ι (TS.doneTS _ _)    = refl

lnDirOf-ι : {X : Set 0ℓ} (e₁ : LNp.LNEv X) → dirOf (ιLN e₁) ≡ lnEvDir e₁
lnDirOf-ι (LNp.sendLN _ _)    = refl
lnDirOf-ι (LNp.receiveLN _ _) = refl
lnDirOf-ι (LNp.apiLNev _ _ _) = refl
lnDirOf-ι (LNp.doneLN _ _)    = refl

lfDirOf-ι : {X : Set 0ℓ} (e₁ : LFp.LFEv X) → dirOf (ιLF e₁) ≡ lfEvDir e₁
lfDirOf-ι (LFp.sendLF _ _)    = refl
lfDirOf-ι (LFp.receiveLF _ _) = refl
lfDirOf-ι (LFp.apiLFev _ _ _) = refl
lfDirOf-ι (LFp.doneLF _ _)    = refl

-- CLIENT role-injection: an augmented client io-sim result yields the client
-- half `(dirOf e ≡ cl × ClientIo e a)` of the bundle role disjunction
mkInjC : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {cl : Dir}
    {E₁ : Set 0ℓ} (ι : E₁ → Net_Api Payload X) (edir : E₁ → Dir)
    (bridge : (x : E₁) → dirOf (ι x) ≡ edir x)
  → Σ[ e₁ ∈ E₁ ] (e ≡ ι e₁) × (edir e₁ ≡ cl) × ClientIo (ι e₁) a
  → (dirOf e ≡ cl) × ClientIo e a
mkInjC ι edir bridge (e₁ , iota , d , ci) =
    trans (cong dirOf iota) (trans (bridge e₁) d)
  , subst (λ z → ClientIo z _) (sym iota) ci

-- SERVER role-injection (mirror, ServerIo)
mkInjS : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {sv : Dir}
    {E₁ : Set 0ℓ} (ι : E₁ → Net_Api Payload X) (edir : E₁ → Dir)
    (bridge : (x : E₁) → dirOf (ι x) ≡ edir x)
  → Σ[ e₁ ∈ E₁ ] (e ≡ ι e₁) × (edir e₁ ≡ sv) × ServerIo (ι e₁) a
  → (dirOf e ≡ sv) × ServerIo e a
mkInjS ι edir bridge (e₁ , iota , d , si) =
    trans (cong dirOf iota) (trans (bridge e₁) d)
  , subst (λ z → ServerIo z _) (sym iota) si

------------------------------------------------------------------------
-- ITEM 3b-part2 — `bundleX-io-role` ×6 : byte-copies of the committed
-- `bundleX-ev-link` 12-peer peels with the two driven-peer branches routed to
-- the role injections; every sibling non-offer refutation verbatim.
------------------------------------------------------------------------

-- bundleCS-io-role : role fingerprint of a CS-image bundle io step
bundleCS-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► Bd′
  → (dirOf (ιCS e₁) ≡ cl × ClientIo (ιCS e₁) a) ⊎ (dirOf (ιCS e₁) ≡ sv × ServerIo (ιCS e₁) a)
bundleCS-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...     | PEA.evL _ sM      = inj₁ (mkInjC ιCS csEvDir csDirOf-ι (simCSc-io l cl csc sM))
...     | PEA.evBoth _ sM sTail =
            ⊥-elim (csTail-css-noOffer l cl sv css bfc bfs ip e₁
                      (λ q → cl≢sv (trans (apiDir-inj (csc-ev-dir l cl csc sM) (csApiDir e₁)) q))
                      (_ , sTail))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = inj₂ (mkInjS ιCS csEvDir csDirOf-ι (simCSs-io l sv css sM))
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

-- bundleBF-io-role : role fingerprint of a BF-image bundle io step
bundleBF-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → (dirOf (ιBF e₁) ≡ cl × ClientIo (ιBF e₁) a) ⊎ (dirOf (ιBF e₁) ≡ sv × ServerIo (ιBF e₁) a)
bundleBF-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...         | PEA.evL _ sM      = inj₁ (mkInjC ιBF bfEvDir bfDirOf-ι (simBFc-io l cl bfc sM))
...         | PEA.evBoth _ sM sTail =
              ⊥-elim (bfTail-bfs-noOffer l cl sv bfs ip e₁
                        (λ q → cl≢sv (trans (apiDir-inj (bfc-ev-dir l cl bfc sM) (bfApiDir e₁)) q))
                        (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = inj₂ (mkInjS ιBF bfEvDir bfDirOf-ι (simBFs-io l sv bfs sM))
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

-- bundleKA-io-role : role fingerprint of a KA-image bundle io step
bundleKA-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► Bd′
  → (dirOf (ιKA e₁) ≡ cl × ClientIo (ιKA e₁) a) ⊎ (dirOf (ιKA e₁) ≡ sv × ServerIo (ιKA e₁) a)
bundleKA-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = inj₁ (mkInjC ιKA kaEvDir kaDirOf-ι (simKAc-io l cl (kac ip) sM))
... | PEA.evBoth _ sM sTail =
        ⊥-elim (kaTail-kas-noOffer l cl sv csc css bfc bfs ip e₁
                  (λ q → cl≢sv (trans (apiDir-inj (kac-ev-dir l cl (kac ip) sM) (kaApiDir e₁)) q))
                  (_ , sTail))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = inj₂ (mkInjS ιKA kaEvDir kaDirOf-ι (simKAs-io l sv (kas ip) sM))
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

-- bundleTS-io-role : role fingerprint of a TS-image bundle io step
bundleTS-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► Bd′
  → (dirOf (ιTS e₁) ≡ cl × ClientIo (ιTS e₁) a) ⊎ (dirOf (ιTS e₁) ≡ sv × ServerIo (ιTS e₁) a)
bundleTS-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...             | PEA.evL _ sM = inj₁ (mkInjC ιTS tsEvDir tsDirOf-ι (simTSc-io l cl (tsc ip) sM))
...             | PEA.evBoth _ sM sTail =
                    ⊥-elim (tsTail-tss-noOffer l cl sv ip e₁
                              (λ q → cl≢sv (trans (apiDir-inj (tsc-ev-dir l cl (tsc ip) sM) (tsApiDir e₁)) q))
                              (_ , sTail))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = inj₂ (mkInjS ιTS tsEvDir tsDirOf-ι (simTSs-io l sv (tss ip) sM))
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

-- bundleLN-io-role : role fingerprint of a LN-image bundle io step
bundleLN-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► Bd′
  → (dirOf (ιLN e₁) ≡ cl × ClientIo (ιLN e₁) a) ⊎ (dirOf (ιLN e₁) ≡ sv × ServerIo (ιLN e₁) a)
bundleLN-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...                 | PEA.evL _ sM = inj₁ (mkInjC ιLN lnEvDir lnDirOf-ι (simLNc-io l cl (lnc ip) sM))
...                 | PEA.evBoth _ sM sTail =
                        ⊥-elim (lnTail-lns-noOffer l cl sv ip e₁
                                  (λ q → cl≢sv (trans (apiDir-inj (lnc-ev-dir l cl (lnc ip) sM) (lnApiDir e₁)) q))
                                  (_ , sTail))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = inj₂ (mkInjS ιLN lnEvDir lnDirOf-ι (simLNs-io l sv (lns ip) sM))
...                   | PEA.evBoth _ sM sTail =
                          ⊥-elim (lnTail-lfc-noOffer l cl sv ip e₁ (_ , sTail))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιLN e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιLN e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιLN e₁) (_ , qs))

-- bundleLF-io-role : role fingerprint of a LF-image bundle io step
bundleLF-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► Bd′
  → (dirOf (ιLF e₁) ≡ cl × ClientIo (ιLF e₁) a) ⊎ (dirOf (ιLF e₁) ≡ sv × ServerIo (ιLF e₁) a)
bundleLF-io-role l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...                     | PEA.evL _ sM = inj₁ (mkInjC ιLF lfEvDir lfDirOf-ι (simLFc-io l cl (lfc ip) sM))
...                     | PEA.evBoth _ sM sTail =
                          ⊥-elim (decLFs-dir-noOffer l sv (lfs ip) e₁
                            (λ q → cl≢sv (trans (apiDir-inj (lfc-ev-dir l cl (lfc ip) sM) (lfApiDir e₁)) q))
                            (_ , sTail))
...                     | PEA.evR _ qs = inj₂ (mkInjS ιLF lfEvDir lfDirOf-ι (simLFs-io l sv (lfs ip) qs))

------------------------------------------------------------------------
-- `bundleG-io-role` : generic dispatcher over `e`, mirror of `bundleG-io-ahl`;
-- routes each io channel to its `bundleX-io-role`, non-io killed by `iomem`.
------------------------------------------------------------------------
bundleG-io-role : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → (dirOf e ≡ cl × ClientIo e a) ⊎ (dirOf e ≡ sv × ServerIo e a)
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_ChainSync}   iomem step = bundleCS-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.sendCS    l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_ChainSync}   iomem step = bundleCS-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.receiveCS l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_BlockFetch}  iomem step = bundleBF-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.sendBF    l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_BlockFetch}  iomem step = bundleBF-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.receiveBF l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_KeepAlive}   iomem step = bundleKA-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.sendKA    l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_KeepAlive}   iomem step = bundleKA-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.receiveKA l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_TxSubmission} iomem step = bundleTS-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.sendTS    l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_TxSubmission} iomem step = bundleTS-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.receiveTS l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosNotify} iomem step = bundleLN-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.sendLN   l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosNotify} iomem step = bundleLN-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.receiveLN l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosFetch}  iomem step = bundleLF-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.sendLF   l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosFetch}  iomem step = bundleLF-io-role l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.receiveLF l′ d′} step
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = done   _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiCS  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiBF  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiKA  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiTS  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiLN  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = apiLF  _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} iomem step = ⊥-elim iomem
bundleG-io-role l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- ITEM 3c — concrete io node disjointness.  Each node offers io only on its
-- two links, with a fixed (dir,role) fingerprint per link; adjacent nodes on a
-- shared link hold SWAPPED (cl,sv) so any coincident io event clashes either
-- on direction (`lo≢hi`) or on role (`client-server-excl`).  Non-adjacent nodes
-- differ on the link (`apiLink-inj`).  This is the make-or-break: no `evBoth`.
------------------------------------------------------------------------

-- the per-link (dir,role) fingerprint half of a bundle io offer
RoleFP : {X : Set 0ℓ} → Dir → Dir → Net_Api Payload X → X → Set
RoleFP cl sv e a = (dirOf e ≡ cl × ClientIo e a) ⊎ (dirOf e ≡ sv × ServerIo e a)

-- the two node directions are distinct
lo≢hi : lo ≢ hi
lo≢hi ()

-- remaining distinct-link disequalities not re-exported from SysOracle/SysIoLink
linkAB≢linkCD : ¬ (linkAB ≡ linkCD)
linkAB≢linkCD ()
linkAC≢linkBD : ¬ (linkAC ≡ linkBD)
linkAC≢linkBD ()

-- SHARED-LINK role clash: on a shared `(l,d)` the two adjacent nodes hold
-- swapped `(cl,sv)`; a coincident io event is refuted by direction (`cl≢sv`)
-- or, at equal direction, by role exclusivity (`client-server-excl`).
role-clash : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} (cl sv : Dir) → cl ≢ sv
  → ioES .mem (X , e) a → RoleFP cl sv e a → RoleFP sv cl e a → ⊥
role-clash cl sv cl≢sv iomem (inj₁ (dX , ciX)) (inj₁ (dY , ciY)) = cl≢sv (trans (sym dX) dY)
role-clash cl sv cl≢sv iomem (inj₁ (dX , ciX)) (inj₂ (dY , siY)) = client-server-excl _ _ iomem ciX siY
role-clash cl sv cl≢sv iomem (inj₂ (dX , siX)) (inj₁ (dY , ciY)) = client-server-excl _ _ iomem ciY siX
role-clash cl sv cl≢sv iomem (inj₂ (dX , siX)) (inj₂ (dY , siY)) = cl≢sv (sym (trans (sym dX) dY))


-- the four node io fingerprints (link + per-link (dir,role))
-- node-A io fingerprint: link + (dir,role) read off the firing bundle
nodeA-io-fp : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → ioES .mem (X , e) a
  → SN.decNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
nodeA-io-fp na {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAB = inj₁ (bundleG-io-ahl linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB , bundleG-io-role linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) iomem sBAB)
...   | PEA.evR _ sBAC = inj₂ (bundleG-io-ahl linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC , bundleG-io-role linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) iomem sBAC)

-- node-B io fingerprint: link + (dir,role) read off the firing bundle
nodeB-io-fp : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B′ : NetProc}
  → ioES .mem (X , e) a
  → SN.decNodeB nb ─[ ev (evl (evLabel X e a)) ]─► B′
  → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
nodeB-io-fp nb {X} {e} {a} iomem step
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
...   | PEA.evL _ sBAB = inj₁ (bundleG-io-ahl linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB , bundleG-io-role linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) iomem sBAB)
...   | PEA.evR _ sBBD = inj₂ (bundleG-io-ahl linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD , bundleG-io-role linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) iomem sBBD)

-- node-C io fingerprint: link + (dir,role) read off the firing bundle
nodeC-io-fp : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {C′ : NetProc}
  → ioES .mem (X , e) a
  → SN.decNodeC nc ─[ ev (evl (evLabel X e a)) ]─► C′
  → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
nodeC-io-fp nc {X} {e} {a} iomem step
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
...   | PEA.evL _ sCAC = inj₁ (bundleG-io-ahl linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sCAC , bundleG-io-role linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) iomem sCAC)
...   | PEA.evR _ sCCD = inj₂ (bundleG-io-ahl linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sCCD , bundleG-io-role linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) iomem sCCD)

-- node-D io fingerprint: link + (dir,role) read off the firing bundle
nodeD-io-fp : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {D′ : NetProc}
  → ioES .mem (X , e) a
  → SN.decNodeD nd ─[ ev (evl (evLabel X e a)) ]─► D′
  → (ApiHasLink linkBD e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP hi lo e a)
nodeD-io-fp nd {X} {e} {a} iomem step
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
...   | PEA.evL _ sDBD = inj₁ (bundleG-io-ahl linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sDBD , bundleG-io-role linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) iomem sDBD)
...   | PEA.evR _ sDCD = inj₂ (bundleG-io-ahl linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sDCD , bundleG-io-role linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) iomem sDCD)

------------------------------------------------------------------------
-- pairwise sibling non-offers (io): a node cannot offer an event fired by
-- another node, given the firing node's io fingerprint.
------------------------------------------------------------------------

-- node B when A fires (shared link AB)
nodeB-io-no-when-A : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
  → ¬ IoOffers (SN.decNodeB nb) e a
nodeB-io-no-when-A nb iomem fpA (M , step) with nodeB-io-fp nb iomem step | fpA
... | inj₁ (ahlB , roleB) | inj₁ (ahlA , roleA) = role-clash lo hi lo≢hi iomem roleA roleB
... | inj₁ (ahlB , _)     | inj₂ (ahlA , _)     = linkAB≢linkAC (apiLink-inj ahlB ahlA)
... | inj₂ (ahlB , _)     | inj₁ (ahlA , _)     = linkAB≢linkBD (apiLink-inj ahlA ahlB)
... | inj₂ (ahlB , _)     | inj₂ (ahlA , _)     = linkAC≢linkBD (apiLink-inj ahlA ahlB)

-- node C when A fires (shared link AC)
nodeC-io-no-when-A : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
  → ¬ IoOffers (SN.decNodeC nc) e a
nodeC-io-no-when-A nc iomem fpA (M , step) with nodeC-io-fp nc iomem step | fpA
... | inj₁ (ahlC , roleC) | inj₂ (ahlA , roleA) = role-clash lo hi lo≢hi iomem roleA roleC
... | inj₁ (ahlC , _)     | inj₁ (ahlA , _)     = linkAB≢linkAC (apiLink-inj ahlA ahlC)
... | inj₂ (ahlC , _)     | inj₁ (ahlA , _)     = linkAB≢linkCD (apiLink-inj ahlA ahlC)
... | inj₂ (ahlC , _)     | inj₂ (ahlA , _)     = linkAC≢linkCD (apiLink-inj ahlA ahlC)

-- node D when A fires (no shared link)
nodeD-io-no-when-A : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP lo hi e a) ⊎ (ApiHasLink linkAC e × RoleFP lo hi e a)
  → ¬ IoOffers (SN.decNodeD nd) e a
nodeD-io-no-when-A nd iomem fpA (M , step) with nodeD-io-fp nd iomem step | fpA
... | inj₁ (ahlD , _) | inj₁ (ahlA , _) = linkAB≢linkBD (apiLink-inj ahlA ahlD)
... | inj₁ (ahlD , _) | inj₂ (ahlA , _) = linkAC≢linkBD (apiLink-inj ahlA ahlD)
... | inj₂ (ahlD , _) | inj₁ (ahlA , _) = linkAB≢linkCD (apiLink-inj ahlA ahlD)
... | inj₂ (ahlD , _) | inj₂ (ahlA , _) = linkAC≢linkCD (apiLink-inj ahlA ahlD)

-- node C when B fires (no shared link)
nodeC-io-no-when-B : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
  → ¬ IoOffers (SN.decNodeC nc) e a
nodeC-io-no-when-B nc iomem fpB (M , step) with nodeC-io-fp nc iomem step | fpB
... | inj₁ (ahlC , _) | inj₁ (ahlB , _) = linkAB≢linkAC (apiLink-inj ahlB ahlC)
... | inj₁ (ahlC , _) | inj₂ (ahlB , _) = linkAC≢linkBD (apiLink-inj ahlC ahlB)
... | inj₂ (ahlC , _) | inj₁ (ahlB , _) = linkAB≢linkCD (apiLink-inj ahlB ahlC)
... | inj₂ (ahlC , _) | inj₂ (ahlB , _) = linkBD≢linkCD (apiLink-inj ahlB ahlC)

-- node D when B fires (shared link BD)
nodeD-io-no-when-B : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAB e × RoleFP hi lo e a) ⊎ (ApiHasLink linkBD e × RoleFP lo hi e a)
  → ¬ IoOffers (SN.decNodeD nd) e a
nodeD-io-no-when-B nd iomem fpB (M , step) with nodeD-io-fp nd iomem step | fpB
... | inj₁ (ahlD , roleD) | inj₂ (ahlB , roleB) = role-clash lo hi lo≢hi iomem roleB roleD
... | inj₁ (ahlD , _)     | inj₁ (ahlB , _)     = linkAB≢linkBD (apiLink-inj ahlB ahlD)
... | inj₂ (ahlD , _)     | inj₁ (ahlB , _)     = linkAB≢linkCD (apiLink-inj ahlB ahlD)
... | inj₂ (ahlD , _)     | inj₂ (ahlB , _)     = linkBD≢linkCD (apiLink-inj ahlB ahlD)

-- node D when C fires (shared link CD)
nodeD-io-no-when-C : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (ApiHasLink linkAC e × RoleFP hi lo e a) ⊎ (ApiHasLink linkCD e × RoleFP lo hi e a)
  → ¬ IoOffers (SN.decNodeD nd) e a
nodeD-io-no-when-C nd iomem fpC (M , step) with nodeD-io-fp nd iomem step | fpC
... | inj₂ (ahlD , roleD) | inj₂ (ahlC , roleC) = role-clash lo hi lo≢hi iomem roleC roleD
... | inj₁ (ahlD , _)     | inj₁ (ahlC , _)     = linkAC≢linkBD (apiLink-inj ahlC ahlD)
... | inj₁ (ahlD , _)     | inj₂ (ahlC , _)     = linkBD≢linkCD (apiLink-inj ahlD ahlC)
... | inj₂ (ahlD , _)     | inj₁ (ahlC , _)     = linkAC≢linkCD (apiLink-inj ahlC ahlD)

------------------------------------------------------------------------
-- group non-offers (io): the sibling group of a firing node offers nothing
------------------------------------------------------------------------
groupA-io-no : (na : SN.NodeStateA) (nb : SN.NodeStateB) (nc : SN.NodeStateC) (nd : SN.NodeStateD)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → ioES .mem (X , e) a → SN.decNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → ¬ IoOffers (SN.decNodeB nb ⦀ (SN.decNodeC nc ⦀ SN.decNodeD nd)) e a
groupA-io-no na nb nc nd iomem sA =
  SStep.⦀-noOffer (SN.decNodeB nb) (SN.decNodeC nc ⦀ SN.decNodeD nd)
    (nodeB-io-no-when-A nb iomem fpA)
    (SStep.⦀-noOffer (SN.decNodeC nc) (SN.decNodeD nd) (nodeC-io-no-when-A nc iomem fpA) (nodeD-io-no-when-A nd iomem fpA))
  where fpA = nodeA-io-fp na iomem sA

groupB-io-no : (nb : SN.NodeStateB) (nc : SN.NodeStateC) (nd : SN.NodeStateD)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B′ : NetProc}
  → ioES .mem (X , e) a → SN.decNodeB nb ─[ ev (evl (evLabel X e a)) ]─► B′
  → ¬ IoOffers (SN.decNodeC nc ⦀ SN.decNodeD nd) e a
groupB-io-no nb nc nd iomem sB =
  SStep.⦀-noOffer (SN.decNodeC nc) (SN.decNodeD nd) (nodeC-io-no-when-B nc iomem fpB) (nodeD-io-no-when-B nd iomem fpB)
  where fpB = nodeB-io-fp nb iomem sB

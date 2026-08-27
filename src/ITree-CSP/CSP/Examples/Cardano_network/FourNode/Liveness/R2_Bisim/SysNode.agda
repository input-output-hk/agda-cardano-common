{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R1 — NODE-A sub-decode (`Praos.SysNode`), Task 3a (CRUX).
--
-- The node-A factor of the whole-system decode `⟦_⟧ : SysState → NetProc`.
-- `nodeA` (FourNodeDiamond.nodeA) is a PRODUCER node:
--
--   nodeA = (miniProtocols linkAB lo hi ⦀ miniProtocols linkAC lo hi)
--             ∥⇘ apiES ⇙ (produce linkAB hi blkA ⦀ produce linkAC hi blkA)
--
-- Each `miniProtocols l lo hi` interleaves the twelve mini-protocol peers
-- (NetworkPar.435): KA / CS / BF / TS / LN / LF, client on `lo`, server on
-- `hi`.  Of the six protocols, FOUR are INERT under Praos (KeepAlive,
-- TxSubmission, LeiosNotify, LeiosFetch — client+server = eight peers): they
-- are api-gated and the node never offers their api events, so they never
-- step and are rebuilt as their literal initial builders.  The remaining two
-- protocols (ChainSync, BlockFetch — client+server) are the DRIVEN peers; the
-- server peers on `hi` are advanced by `produce` via `apiCS`/`apiBF`.
--
-- The abstract node-A position (`NodeStateA`) therefore records, per link:
-- the FSM position of each of the four CS/BF peers plus the `produce` driver
-- phase; the eight inert peers contribute NO state component.  `decNodeA`
-- rebuilds the interleaved bundle INLINE (the peers in the exact
-- `miniProtocols` order — `⦀` regroups only up-to-bisim, not `≡`, so the
-- Task-2 `decInert` contiguous block is NOT a sub-term and is not spliced;
-- it has been removed) with:
--   · each CS/BF peer at its FSM-state loop-head derivative — the REAL
--     renamed FSM `RenCS.renameMap (iter (serverStep l d) st)` (definitionally
--     the NetworkPar builder at `st = stIdle`), NOT the τ-free PipePair spec;
--   · the `produce` driver at its position-derived derivative (the literal
--     prefix-chain tail, i.e. the genuine successor of `produce l d blkA`).
-- `decNodeA-home` is GENUINE (`refl`): at the initial position every peer
-- decodes to its NetworkPar builder and `produce` to its whole body, so the
-- inline reconstruction is definitionally `nodeA` — no WHNF forcing.
--
-- R1/R2 boundary: this delivers the node-A state TYPE, a TOTAL decode, and
-- the INIT home-equality.  Non-init decode branches are DEFINED (totality)
-- but not proven correct — that (plus the transition relation / measure) is
-- R2.  SCOPE NOTE: the CS/BF peers are decoded at LOOP-HEAD granularity
-- (`iter step st`); the mid-step intermediate derivatives (the succV react
-- leaves and loop re-entry sils that a full R2-adequate reconstruction needs)
-- are NOT yet represented — see the Task-3a report for the precise per-peer
-- succV sub-split.  `produce` is represented at full step granularity.
--
-- No postulates, holes, or `--allow-unsolved-metas` (R1 must be genuine).
------------------------------------------------------------------------

open import Level using (0ℓ)
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Class.DecEq using (DecEq)
import Class.DecEq.Instances as DecEqI

open import Process_Trees using (PTree; ExtI; AnyTypes; NodeKind; react)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode (blkA : Block₃) where

------------------------------------------------------------------------
-- The concrete model under study (Phase-1, `examples/praos_liveness`).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; nodeA; nodeB; nodeC; nodeD; produce; consume; consume-k; Block₃
        ; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p using ( time₀; length₀; Block; Cookie; VoteBlob; Txid; decCookie; LFBitmap )
open import CSP.Examples.Cardano_network.Base using (Dir; lo; hi; FromInitiator; N2N_ChainSync; N2N_BlockFetch; BlockingStyle; Blocking; NonBlocking)
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; done
        ; apiCS; apiBF
        ; reqCSRequestNext; sendCSRollForward; sendCSAwaitReply
        ; reqBFRange; sendBFStartBatch; sendBFBlock; sendBFBatchDone
        ; sendCSRequestNext; recvCSRollforward; sendCSDone
        ; sendBFRequestRange; recvBFBlock; sendBFClientDone
        ; sendCSFindIntersect; sendCSRollBackward
        ; sendCSIntersectFound; sendCSIntersectNotFound; sendBFNoBlocks
        ; errCookie; sendKAMsg; sendKADone
        ; sendLNRequestNext; sendLNDone; sendLNBlockAnnouncement
        ; sendLNBlockOffer; sendLNBlockTxsOffer; sendLNVotesOffer
        ; sendTSReplyTxIds; sendTSReplyTxs; sendTSDone
        ; sendTSRequestTxIdsBlocking; sendTSRequestTxIdsPipelined; sendTSRequestTxsPipelined
        ; sendLFBlockRequest; sendLFBlockTxsRequest; sendLFVotesRequest
        ; sendLFBlockRangeRequest; sendLFDone; sendLFBlock; sendLFBlockTxs
        ; sendLFVoteDelivery; sendLFNextBlockAndTxsInRange; sendLFLastBlockAndTxsInRange )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; Header; Tip; header; tip; DecEq-Header; DecEq-Tip
        ; Point; ChainRange; point; chainRange; DecEq-ChainRange
        ; chainSync; blockFetch; keepAlive; leiosNotify; leiosFetch
        ; MsgKeepAlive; MsgKADone; MsgLNDone; MsgLFDone
        ; MsgLNBlockAnnouncement; MsgLNBlockOffer; MsgLNBlockTxsOffer; MsgLNVotesOffer; Vote
        ; MsgLFBlock; MsgLFBlockTxs; MsgLFVoteDelivery
        ; MsgLFNextBlockAndTxsInRange; MsgLFLastBlockAndTxsInRange; Tx
        ; txSubmission; MsgTSRequestTxIds; MsgTSRequestTxs; MsgTSDone
        ; MsgCSRequestNext; MsgCSFindIntersect; MsgCSDone
        ; MsgCSRollForward; MsgCSRollBackward; MsgCSAwaitReply
        ; MsgCSIntersectFound; MsgCSIntersectNotFound
        ; MsgRequestRange; MsgClientDone; MsgStartBatch
        ; MsgNoBlocks; MsgBlock; MsgBatchDone )

-- the eight inert non-Praos peer builders (KA / TS / LN / LF, client+server)
-- and the four driven CS / BF peer builders + the rename injections, verbatim
-- as they appear inside `miniProtocols` (NetworkPar.435)
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( KAclientA; KAserverA
        ; TSclientA; TSserverA
        ; LNclientA; LNserverA
        ; LFclientA; LFserverA
        ; CSclientA; CSserverA; BFclientA; BFserverA
        ; ιCS; ιCS⁻¹; ιCS-linv; ιBF; ιBF⁻¹; ιBF-linv
        ; ιTS; ιTS⁻¹; ιTS-linv
        ; ιKA; ιKA⁻¹; ιKA-linv
        ; ιLN; ιLN⁻¹; ιLN-linv
        ; ιLF; ιLF⁻¹; ιLF-linv )

-- the source ChainSync / BlockFetch / TxSubmission / KeepAlive / LeiosNotify / LeiosFetch FSM modules (state enums + step bodies)
import CSP.Examples.Cardano_network.ChainSync    p as CS
import CSP.Examples.Cardano_network.BlockFetch   p as BF
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.KeepAlive    p as KA
import CSP.Examples.Cardano_network.LeiosNotify  p as LN
import CSP.Examples.Cardano_network.LeiosFetch   p as LF

-- the source-alphabet loop combinator `iter` (same `iter` the peer builders use)
import CSP.Operators {E = CS.CSEv} CS.CSEv-≟ as SrcOpC
import CSP.Operators {E = BF.BFEv} BF.BFEv-≟ as SrcOpB
import CSP.Operators {E = TS.TSEv} TS.TSEv-≟ as SrcOpT
import CSP.Operators {E = KA.KAEv} KA.KAEv-≟ as SrcOpK
import CSP.Operators {E = LN.LNEv} LN.LNEv-≟ as SrcOpN
import CSP.Operators {E = LF.LFEv} LF.LFEv-≟ as SrcOpF

-- the SAME renamings NetworkPar's CS / BF / TS / KA / LN / LF peers use (same ι/ι⁻¹/ι-linv, so
-- `renameMap (iter step stIdle)` matches `CSserverA`/`TSclientA`/`LNclientA`/… definitionally)
import CSP.Rename {E₁ = CS.CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv as RenCS
import CSP.Rename {E₁ = BF.BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RenBF
import CSP.Rename {E₁ = TS.TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv as RenTS
import CSP.Rename {E₁ = KA.KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA
import CSP.Rename {E₁ = LN.LNEv} {E₂ = Net_Api Payload} ιLN ιLN⁻¹ ιLN-linv as RenLN
import CSP.Rename {E₁ = LF.LFEv} {E₂ = Net_Api Payload} ιLF ιLF⁻¹ ιLF-linv as RenLF

-- Net_Api operators (the whole-system alphabet)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _⦀_; _∥⇘_⇙_; Prefix; Prefix₀; Output; Skip; Ret; _>>=_; _>>_ )

-- the whole-system process type (same alias as the spike / `breakableSystem`)
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- product DecEq for the `sendCSRollForward` carrier (Header × Tip), matching
-- FourNodeDiamond's instance so the `produce`-tail `Output` resolves
instance
  DecEq-Header×Tip : DecEq (Header × Tip)
  DecEq-Header×Tip = DecEqI.DecEq-×
  -- Cookie × Cookie DecEq for the KA `errCookie` output payload (kcErr1 leaf)
  DecEq-Cookie² : DecEq (Cookie × Cookie)
  DecEq-Cookie² = DecEqI.DecEq-×

------------------------------------------------------------------------
-- FINE driven-peer decode (R2 Task 2): the REAL renamed CS / BF FSM at its
-- FULL position set — every LTS derivative of the underlying `iter (step) st`
-- loop, not just the loop heads.  A peer position is one of:
--   · a LOOP HEAD `iter (step l d) st` (one per FSM state; `st = stIdle`
--     renames definitionally to the NetworkPar builder — home stays `refl`);
--   · a MID-STEP REACT LEAF, the derivative reached after firing the first
--     (and, for the two-message `Done` branches, second) event of a branch —
--     named via the `succV` successor trick (the `PerLink.Decode` /
--     `SysMedium` pattern) so its `iter-bind`-wrapped normal form is never
--     written by hand; and
--   · a LOOP RE-ENTRY SIL `iter-bind (Ret (inj₁ st′)) (step l d)` (which
--     forces to `sil (iter (step) st′)`), one parametric constructor per
--     target state `st′`.
-- Because renaming is a homomorphism (`RenCS.renameMap` commutes with LTS
-- steps), this source-side set renamed into `Net_Api` is CLOSED under the
-- decoded peer's transitions — the enabling invariant R2 Task 4 needs.
------------------------------------------------------------------------

-- the ChainSync / BlockFetch peer process types over their source alphabets
CSProc : Set₁
CSProc = PTree CS.CSEv (ExtI CS.CSEv) CS.Rr
BFProc : Set₁
BFProc = PTree BF.BFEv (ExtI BF.BFEv) BF.Rr
TSProc : Set₁
TSProc = PTree TS.TSEv (ExtI TS.TSEv) TS.Rr
KAProc : Set₁
KAProc = PTree KA.KAEv (ExtI KA.KAEv) KA.Rr
LNProc : Set₁
LNProc = PTree LN.LNEv (ExtI LN.LNEv) LN.Rr
LFProc : Set₁
LFProc = PTree LF.LFEv (ExtI LF.LFEv) LF.Rr

-- the visible-offer map of a ChainSync node (empty for non-react nodes)
vis-ofC : NodeKind CS.CSEv (ExtI CS.CSEv) CS.Rr
        → (at : AnyTypes CS.CSEv) → proj₁ at → Maybe CSProc
vis-ofC (react v _) = v
vis-ofC _           = λ _ _ → nothing

-- visible successor of `q` along `at`/`a` (identity if not offered) — CS
succVC : CSProc → (at : AnyTypes CS.CSEv) → proj₁ at → CSProc
succVC q at a with vis-ofC (PTree.force q) at a
... | just t  = t
... | nothing = q

-- the visible-offer map of a BlockFetch node (empty for non-react nodes)
vis-ofB : NodeKind BF.BFEv (ExtI BF.BFEv) BF.Rr
        → (at : AnyTypes BF.BFEv) → proj₁ at → Maybe BFProc
vis-ofB (react v _) = v
vis-ofB _           = λ _ _ → nothing

-- visible successor of `q` along `at`/`a` (identity if not offered) — BF
succVB : BFProc → (at : AnyTypes BF.BFEv) → proj₁ at → BFProc
succVB q at a with vis-ofB (PTree.force q) at a
... | just t  = t
... | nothing = q

-- the visible-offer map of a KeepAlive node (empty for non-react nodes)
vis-ofK : NodeKind KA.KAEv (ExtI KA.KAEv) KA.Rr
        → (at : AnyTypes KA.KAEv) → proj₁ at → Maybe KAProc
vis-ofK (react v _) = v
vis-ofK _           = λ _ _ → nothing

-- visible successor of `q` along `at`/`a` (identity if not offered) — KA
succVK : KAProc → (at : AnyTypes KA.KAEv) → proj₁ at → KAProc
succVK q at a with vis-ofK (PTree.force q) at a
... | just t  = t
... | nothing = q

-- the visible-offer map of a LeiosNotify node (empty for non-react nodes)
vis-ofN : NodeKind LN.LNEv (ExtI LN.LNEv) LN.Rr
        → (at : AnyTypes LN.LNEv) → proj₁ at → Maybe LNProc
vis-ofN (react v _) = v
vis-ofN _           = λ _ _ → nothing

-- visible successor of `q` along `at`/`a` (identity if not offered) — LN
succVN : LNProc → (at : AnyTypes LN.LNEv) → proj₁ at → LNProc
succVN q at a with vis-ofN (PTree.force q) at a
... | just t  = t
... | nothing = q

-- the visible-offer map of a LeiosFetch node (empty for non-react nodes)
vis-ofF : NodeKind LF.LFEv (ExtI LF.LFEv) LF.Rr
        → (at : AnyTypes LF.LFEv) → proj₁ at → Maybe LFProc
vis-ofF (react v _) = v
vis-ofF _           = λ _ _ → nothing

-- visible successor of `q` along `at`/`a` (identity if not offered) — LF
succVF : LFProc → (at : AnyTypes LF.LFEv) → proj₁ at → LFProc
succVF q at a with vis-ofF (PTree.force q) at a
... | just t  = t
... | nothing = q

-- the visible-offer map of a TxSubmission node (empty for non-react nodes)
vis-ofT : NodeKind TS.TSEv (ExtI TS.TSEv) TS.Rr
        → (at : AnyTypes TS.TSEv) → proj₁ at → Maybe TSProc
vis-ofT (react v _) = v
vis-ofT _           = λ _ _ → nothing

-- visible successor of `q` along `at`/`a` (identity if not offered) — TS
succVT : TSProc → (at : AnyTypes TS.TSEv) → proj₁ at → TSProc
succVT q at a with vis-ofT (PTree.force q) at a
... | just t  = t
... | nothing = q

------------------------------------------------------------------------
-- ChainSync CLIENT positions (client offers api at stIdle; receives on the
-- wire at stCanAwait/stMustReply/stIntersect).  `csHead st` is a loop head;
-- `csSil st` a loop re-entry.  The `csRF1`/`csRB1` leaves are shared by the
-- stCanAwait and stMustReply RollForward/RollBackward branches (identical
-- delivery derivative → stIdle).
------------------------------------------------------------------------

-- the fine ChainSync-client position
data CScPos : Set where
  csHead     : CS.CSState → CScPos          -- loop head `iter (clientStep) st`
  csReqNext1 : CScPos                        -- stIdle: offers `sendCS!` (RequestNext) → csSil stCanAwait
  csFindInt1 : List Point → CScPos           -- stIdle: offers `sendCS!` (FindIntersect ps) → csSil stIntersect
  csDone1    : CScPos                        -- stIdle: offers `sendCS!` (Done) → csSil stDone (client has no node-local done)
  csRF1      : Header → Tip → CScPos         -- recv RollForward: offers `apiCSev recvCSRollforward!` → csSil stIdle
  csRB1      : Point → Tip → CScPos          -- recv RollBackward: offers `apiCSev recvCSRollback!` → csSil stIdle
  csIF1      : Point → Tip → CScPos          -- recv IntersectFound: offers `apiCSev recvCSIntersectFound!` → csSil stIdle
  csINF1     : Tip → CScPos                  -- recv IntersectNotFound: offers `apiCSev recvCSIntersectNotFound!` → csSil stIdle
  csSil      : CS.CSState → CScPos           -- loop re-entry `iter-bind (Ret (inj₁ st)) (clientStep)`

-- source-side decode of the ChainSync client peer at a fine position
decCSc-src : Link → Dir → CScPos → CSProc
decCSc-src l d (csHead st)     = SrcOpC.iter (CS.clientStep l d) st
decCSc-src l d csReqNext1      =
  succVC (SrcOpC.iter (CS.clientStep l d) CS.stIdle) (_ , CS.apiCSev l d sendCSRequestNext) U.tt
decCSc-src l d (csFindInt1 ps) =
  succVC (SrcOpC.iter (CS.clientStep l d) CS.stIdle) (_ , CS.apiCSev l d sendCSFindIntersect) ps
decCSc-src l d csDone1         =
  succVC (SrcOpC.iter (CS.clientStep l d) CS.stIdle) (_ , CS.apiCSev l d sendCSDone) U.tt
decCSc-src l d (csRF1 h t)     =
  succVC (SrcOpC.iter (CS.clientStep l d) CS.stCanAwait) (_ , CS.receiveCS l d)
         (time₀ , FromInitiator , length₀ , chainSync (MsgCSRollForward h t))
decCSc-src l d (csRB1 pt tp)   =
  succVC (SrcOpC.iter (CS.clientStep l d) CS.stCanAwait) (_ , CS.receiveCS l d)
         (time₀ , FromInitiator , length₀ , chainSync (MsgCSRollBackward pt tp))
decCSc-src l d (csIF1 pt tp)   =
  succVC (SrcOpC.iter (CS.clientStep l d) CS.stIntersect) (_ , CS.receiveCS l d)
         (time₀ , FromInitiator , length₀ , chainSync (MsgCSIntersectFound pt tp))
decCSc-src l d (csINF1 tp)     =
  succVC (SrcOpC.iter (CS.clientStep l d) CS.stIntersect) (_ , CS.receiveCS l d)
         (time₀ , FromInitiator , length₀ , chainSync (MsgCSIntersectNotFound tp))
decCSc-src l d (csSil st)      =
  SrcOpC.iter-bind (SrcOpC.Ret (inj₁ st)) (CS.clientStep l d)

------------------------------------------------------------------------
-- ChainSync SERVER positions (receives requests on the wire at stIdle;
-- application drives via api at stCanAwait/stMustReply/stIntersect).  The
-- `ssRF1`/`ssRB1` leaves are shared by the stCanAwait and stMustReply
-- RollForward/RollBackward branches (identical `sendCS!` derivative → stIdle).
------------------------------------------------------------------------

-- the fine ChainSync-server position
data CSsPos : Set where
  ssHead     : CS.CSState → CSsPos          -- loop head `iter (serverStep) st`
  ssReqNext1 : CSsPos                        -- stIdle recv RequestNext: offers `apiCSev reqCSRequestNext` → ssSil stCanAwait
  ssFindInt1 : List Point → CSsPos           -- stIdle recv FindIntersect: offers `apiCSev reqCSFindIntersect!` → ssSil stIntersect
  ssDone1    : CSsPos                        -- stIdle recv Done: offers `doneCS` → ssSil stDone
  ssRF1      : Header → Tip → CSsPos         -- api RollForward: offers `sendCS!` → ssSil stIdle
  ssRB1      : Point → Tip → CSsPos          -- api RollBackward: offers `sendCS!` → ssSil stIdle
  ssAw1      : CSsPos                        -- api AwaitReply: offers `sendCS!` → ssSil stMustReply
  ssIF1      : Point → Tip → CSsPos          -- api IntersectFound: offers `sendCS!` → ssSil stIdle
  ssINF1     : Tip → CSsPos                  -- api IntersectNotFound: offers `sendCS!` → ssSil stIdle
  ssSil      : CS.CSState → CSsPos           -- loop re-entry `iter-bind (Ret (inj₁ st)) (serverStep)`

-- source-side decode of the ChainSync server peer at a fine position
decCSs-src : Link → Dir → CSsPos → CSProc
decCSs-src l d (ssHead st)     = SrcOpC.iter (CS.serverStep l d) st
decCSs-src l d ssReqNext1      =
  succVC (SrcOpC.iter (CS.serverStep l d) CS.stIdle) (_ , CS.receiveCS l d)
         (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
decCSs-src l d (ssFindInt1 ps) =
  succVC (SrcOpC.iter (CS.serverStep l d) CS.stIdle) (_ , CS.receiveCS l d)
         (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
decCSs-src l d ssDone1         =
  succVC (SrcOpC.iter (CS.serverStep l d) CS.stIdle) (_ , CS.receiveCS l d)
         (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
decCSs-src l d (ssRF1 h t)     =
  succVC (SrcOpC.iter (CS.serverStep l d) CS.stCanAwait) (_ , CS.apiCSev l d sendCSRollForward) (h , t)
decCSs-src l d (ssRB1 pt tp)   =
  succVC (SrcOpC.iter (CS.serverStep l d) CS.stCanAwait) (_ , CS.apiCSev l d sendCSRollBackward) (pt , tp)
decCSs-src l d ssAw1           =
  succVC (SrcOpC.iter (CS.serverStep l d) CS.stCanAwait) (_ , CS.apiCSev l d sendCSAwaitReply) U.tt
decCSs-src l d (ssIF1 pt tp)   =
  succVC (SrcOpC.iter (CS.serverStep l d) CS.stIntersect) (_ , CS.apiCSev l d sendCSIntersectFound) (pt , tp)
decCSs-src l d (ssINF1 tp)     =
  succVC (SrcOpC.iter (CS.serverStep l d) CS.stIntersect) (_ , CS.apiCSev l d sendCSIntersectNotFound) tp
decCSs-src l d (ssSil st)      =
  SrcOpC.iter-bind (SrcOpC.Ret (inj₁ st)) (CS.serverStep l d)

------------------------------------------------------------------------
-- BlockFetch CLIENT positions (client offers api at stIdle; receives on the
-- wire at stBusy/stStreaming).  The stBusy StartBatch/NoBlocks and the
-- stStreaming BatchDone branches step straight to a loop re-entry (`bcSil`);
-- only `MsgBlock b` and the two-message `ClientDone` branch add react leaves.
------------------------------------------------------------------------

-- the fine BlockFetch-client position
data BFcPos : Set where
  bcHead  : BF.BFState → BFcPos             -- loop head `iter (clientStep) st`
  bcReq1  : ChainRange → BFcPos             -- stIdle: offers `sendBF!` (RequestRange r) → bcSil stBusy
  bcDone1 : BFcPos                          -- stIdle: offers `sendBF!` (ClientDone) → bcSil stDone (client has no node-local done)
  bcBlk1  : Block → BFcPos                  -- stStreaming recv Block: offers `apiBFev recvBFBlock!` → bcSil stStreaming
  bcSil   : BF.BFState → BFcPos             -- loop re-entry `iter-bind (Ret (inj₁ st)) (clientStep)`

-- source-side decode of the BlockFetch client peer at a fine position
decBFc-src : Link → Dir → BFcPos → BFProc
decBFc-src l d (bcHead st)  = SrcOpB.iter (BF.clientStep l d) st
decBFc-src l d (bcReq1 r)   =
  succVB (SrcOpB.iter (BF.clientStep l d) BF.stIdle) (_ , BF.apiBFev l d sendBFRequestRange) r
decBFc-src l d bcDone1      =
  succVB (SrcOpB.iter (BF.clientStep l d) BF.stIdle) (_ , BF.apiBFev l d sendBFClientDone) U.tt
decBFc-src l d (bcBlk1 b)   =
  succVB (SrcOpB.iter (BF.clientStep l d) BF.stStreaming) (_ , BF.receiveBF l d)
         (time₀ , FromInitiator , length₀ , blockFetch (MsgBlock b))
decBFc-src l d (bcSil st)   =
  SrcOpB.iter-bind (SrcOpB.Ret (inj₁ st)) (BF.clientStep l d)

------------------------------------------------------------------------
-- BlockFetch SERVER positions (receives a request on the wire at stIdle;
-- application drives via api at stBusy/stStreaming).
------------------------------------------------------------------------

-- the fine BlockFetch-server position
data BFsPos : Set where
  bsHead       : BF.BFState → BFsPos        -- loop head `iter (serverStep) st`
  bsReq1       : ChainRange → BFsPos        -- stIdle recv RequestRange: offers `apiBFev reqBFRange!` → bsSil stBusy
  bsDone1      : BFsPos                     -- stIdle recv ClientDone: offers `doneBF` → bsSil stDone
  bsStart1     : BFsPos                     -- api StartBatch: offers `sendBF!` → bsSil stStreaming
  bsNoBlk1     : BFsPos                     -- api NoBlocks: offers `sendBF!` → bsSil stIdle
  bsBlk1       : Block → BFsPos             -- api Block: offers `sendBF!` (Block b) → bsSil stStreaming
  bsBatchDone1 : BFsPos                     -- api BatchDone: offers `sendBF!` → bsSil stIdle
  bsSil        : BF.BFState → BFsPos        -- loop re-entry `iter-bind (Ret (inj₁ st)) (serverStep)`

-- source-side decode of the BlockFetch server peer at a fine position
decBFs-src : Link → Dir → BFsPos → BFProc
decBFs-src l d (bsHead st)   = SrcOpB.iter (BF.serverStep l d) st
decBFs-src l d (bsReq1 r)    =
  succVB (SrcOpB.iter (BF.serverStep l d) BF.stIdle) (_ , BF.receiveBF l d)
         (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
decBFs-src l d bsDone1       =
  succVB (SrcOpB.iter (BF.serverStep l d) BF.stIdle) (_ , BF.receiveBF l d)
         (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
decBFs-src l d bsStart1      =
  succVB (SrcOpB.iter (BF.serverStep l d) BF.stBusy) (_ , BF.apiBFev l d sendBFStartBatch) U.tt
decBFs-src l d bsNoBlk1      =
  succVB (SrcOpB.iter (BF.serverStep l d) BF.stBusy) (_ , BF.apiBFev l d sendBFNoBlocks) U.tt
decBFs-src l d (bsBlk1 b)    =
  succVB (SrcOpB.iter (BF.serverStep l d) BF.stStreaming) (_ , BF.apiBFev l d sendBFBlock) b
decBFs-src l d bsBatchDone1  =
  succVB (SrcOpB.iter (BF.serverStep l d) BF.stStreaming) (_ , BF.apiBFev l d sendBFBatchDone) U.tt
decBFs-src l d (bsSil st)    =
  SrcOpB.iter-bind (SrcOpB.Ret (inj₁ st)) (BF.serverStep l d)

------------------------------------------------------------------------
-- TxSubmission CLIENT / SERVER positions (R2 D3, folded threading).  The TS
-- pair is the ONLY otherwise-inert peer that MOVES undriven: the client
-- auto-sends `MsgTSInit` at its loop head (`stInit`) and then blocks at
-- `stIdle`; the server receives that Init and then blocks at `stIdle`.  Firing
-- the Init io lands directly on a loop re-entry sil (`Ret (inj₁ stIdle)` under
-- `iter-bind`), so — unlike CS/BF — there is NO mid-react leaf: a `…Head`/`…Sil`
-- pair over `TSState` captures every reachable position.  The `…Sil` position
-- carries a GENUINE τ (the loop re-entry), which `bundle-τ-inv` now inverts.
------------------------------------------------------------------------

-- the fine TxSubmission-client position
data TScPos : Set where
  tcHead : TS.TSState → TScPos   -- loop head `iter (clientStep) st`
  tcReqIdsB1  : ℕ → ℕ → TScPos       -- stIdle recv MsgTSRequestTxIds Blocking a r: offers `apiTSev recvTSRequestTxIds! (Blocking,a,r)` (Output) → tcSil stTxIdsBlocking
  tcReqIdsNB1 : ℕ → ℕ → TScPos       -- stIdle recv MsgTSRequestTxIds NonBlocking a r: offers `apiTSev recvTSRequestTxIds! (NonBlocking,a,r)` (Output) → tcSil stTxIdsNonBlocking
  tcReqTxs1   : List Txid → TScPos   -- stIdle recv MsgTSRequestTxs ids: offers `apiTSev recvTSRequestTxs! ids` (Output) → tcSil stTxs
  tcRepB1  : List Txid → TScPos  -- stTxIdsBlocking post-apiTSev sendTSReplyTxIds ids: offers `sendTS!` (MsgTSReplyTxIds ids) → tcSil stIdle (io-case send leaf)
  tcDone1  : TScPos              -- stTxIdsBlocking post-apiTSev sendTSDone: offers `sendTS!` (MsgTSDone) → tcSil stDone (io-case send leaf)
  tcRepNB1 : List Txid → TScPos  -- stTxIdsNonBlocking post-apiTSev sendTSReplyTxIds ids: offers `sendTS!` (MsgTSReplyTxIds ids) → tcSil stIdle
  tcRepTxs1 : List Tx → TScPos   -- stTxs post-apiTSev sendTSReplyTxs txs: offers `sendTS!` (MsgTSReplyTxs txs) → tcSil stIdle
  tcSil  : TS.TSState → TScPos   -- loop re-entry `iter-bind (Ret (inj₁ st)) (clientStep)`

-- source-side decode of the TxSubmission client peer at a fine position
decTSc-src : Link → Dir → TScPos → TSProc
decTSc-src l d (tcHead st) = SrcOpT.iter (TS.clientStep l d) st
decTSc-src l d (tcReqIdsB1 a r)  =
  succVT (SrcOpT.iter (TS.clientStep l d) TS.stIdle) (_ , TS.receiveTS l d)
         (time₀ , FromInitiator , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r))
decTSc-src l d (tcReqIdsNB1 a r) =
  succVT (SrcOpT.iter (TS.clientStep l d) TS.stIdle) (_ , TS.receiveTS l d)
         (time₀ , FromInitiator , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r))
decTSc-src l d (tcReqTxs1 ids)   =
  succVT (SrcOpT.iter (TS.clientStep l d) TS.stIdle) (_ , TS.receiveTS l d)
         (time₀ , FromInitiator , length₀ , txSubmission (MsgTSRequestTxs ids))
decTSc-src l d (tcRepB1 ids)  =
  succVT (SrcOpT.iter (TS.clientStep l d) TS.stTxIdsBlocking) (_ , TS.apiTSev l d sendTSReplyTxIds) ids
decTSc-src l d tcDone1        =
  succVT (SrcOpT.iter (TS.clientStep l d) TS.stTxIdsBlocking) (_ , TS.apiTSev l d sendTSDone) U.tt
decTSc-src l d (tcRepNB1 ids) =
  succVT (SrcOpT.iter (TS.clientStep l d) TS.stTxIdsNonBlocking) (_ , TS.apiTSev l d sendTSReplyTxIds) ids
decTSc-src l d (tcRepTxs1 txs) =
  succVT (SrcOpT.iter (TS.clientStep l d) TS.stTxs) (_ , TS.apiTSev l d sendTSReplyTxs) txs
decTSc-src l d (tcSil st)  = SrcOpT.iter-bind (SrcOpT.Ret (inj₁ st)) (TS.clientStep l d)

-- the fine TxSubmission-server position
data TSsPos : Set where
  tsHead : TS.TSState → TSsPos   -- loop head `iter (serverStep) st`
  tsDone1 : TSsPos               -- stTxIdsBlocking recv MsgTSDone: offers `doneTS` → tsSil stDone (io-case post-receive done leaf)
  tsReqB1  : ℕ × ℕ → TSsPos      -- stIdle post-apiTSev sendTSRequestTxIdsBlocking (a,r): offers `sendTS!` (MsgTSRequestTxIds Blocking a r) → tsSil stTxIdsBlocking (io-case send leaf)
  tsReqNB1 : ℕ × ℕ → TSsPos      -- stIdle post-apiTSev sendTSRequestTxIdsPipelined (a,r): offers `sendTS!` (MsgTSRequestTxIds NonBlocking a r) → tsSil stTxIdsNonBlocking
  tsReqTxs1 : List Txid → TSsPos -- stIdle post-apiTSev sendTSRequestTxsPipelined ids: offers `sendTS!` (MsgTSRequestTxs ids) → tsSil stTxs
  tsSil  : TS.TSState → TSsPos   -- loop re-entry `iter-bind (Ret (inj₁ st)) (serverStep)`

-- source-side decode of the TxSubmission server peer at a fine position
decTSs-src : Link → Dir → TSsPos → TSProc
decTSs-src l d (tsHead st) = SrcOpT.iter (TS.serverStep l d) st
decTSs-src l d tsDone1     =
  succVT (SrcOpT.iter (TS.serverStep l d) TS.stTxIdsBlocking) (_ , TS.receiveTS l d)
         (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone)
decTSs-src l d (tsReqB1 ar)  =
  succVT (SrcOpT.iter (TS.serverStep l d) TS.stIdle) (_ , TS.apiTSev l d sendTSRequestTxIdsBlocking) ar
decTSs-src l d (tsReqNB1 ar) =
  succVT (SrcOpT.iter (TS.serverStep l d) TS.stIdle) (_ , TS.apiTSev l d sendTSRequestTxIdsPipelined) ar
decTSs-src l d (tsReqTxs1 ids) =
  succVT (SrcOpT.iter (TS.serverStep l d) TS.stIdle) (_ , TS.apiTSev l d sendTSRequestTxsPipelined) ids
decTSs-src l d (tsSil st)  = SrcOpT.iter-bind (SrcOpT.Ret (inj₁ st)) (TS.serverStep l d)

------------------------------------------------------------------------
-- KeepAlive CLIENT / SERVER positions (R2 D3, KA uniformity pass).  Both KA
-- peers are FROZEN undriven at their loop head (the client offers only the
-- undriven `apiKAev`; the server offers only the wire `receiveKA` that the
-- client never sends), so the reachable-when-undriven position is the loop
-- head.  Mirroring the TxSubmission pair, a `…Head`/`…Sil` pair over `KAState`
-- captures the head + the loop re-entry sil (the latter is a target of the
-- deferred io co-move; it carries the genuine loop-τ that `bundle-τ-inv` now
-- routes for KA, exactly as for TS).  The post-receive `recvKACookie`-offering
-- mid-react leaf is only reached by firing the wire io and is introduced by
-- the io-case dispatch, not here.
------------------------------------------------------------------------

-- the fine KeepAlive-client position
data KAcPos : Set where
  kcHead : KA.KAState → KAcPos   -- loop head `iter (clientStep) st`
  kcErr1 : (cq cr : Cookie) → ¬ (cq ≡ cr) → KAcPos
                                 -- stServer cq recv MsgKeepAliveResponse cr with cq≢cr:
                                 -- offers `apiKAev errCookie! (cq,cr)` → ksSil stClient (io-case error leaf)
  kcReq1 : Cookie → KAcPos       -- stClient post-apiKAev sendKAMsg c: offers `sendKA!` (MsgKeepAlive c) → kcSil (stServer c) (io-case send leaf)
  kcDone1 : KAcPos               -- stClient post-apiKAev sendKADone: offers `sendKA!` (MsgKADone) → kcSil stDone (io-case send leaf)
  kcSil  : KA.KAState → KAcPos   -- loop re-entry `iter-bind (Ret (inj₁ st)) (clientStep)`
  kcTermE1 : KAcPos              -- √ after the errCookie emit (successor of `kcErr1`:
                                 -- `iter-bind (Ret (inj₂ _)) clientStep`, forces to `ret`;
                                 -- coarsens to the abstract `kcTermE`, distinct from `kcTerm`)

-- source-side decode of the KeepAlive client peer at a fine position
decKAc-src : Link → Dir → KAcPos → KAProc
decKAc-src l d (kcHead st) = SrcOpK.iter (KA.clientStep l d) st
-- error leaf: the succV-successor of `iter clientStep (stServer cq)` along the
-- `receiveKA` fire (with cq≢cr) is, in normal form, the raw errCookie output bound
-- into the loop — written DIRECTLY (sidestepping the stuck `cq ≟ cr` guard of succVK)
decKAc-src l d (kcErr1 cq cr ne) =
  SrcOpK.iter-bind (SrcOpK.Output (KA.apiKAev l d errCookie) (cq , cr) (SrcOpK.Ret (inj₂ _)))
                   (KA.clientStep l d)
-- send leaves: the succV-successor of `iter clientStep stClient` along the api emit
decKAc-src l d (kcReq1 c)  =
  succVK (SrcOpK.iter (KA.clientStep l d) KA.stClient) (_ , KA.apiKAev l d sendKAMsg) c
decKAc-src l d kcDone1     =
  succVK (SrcOpK.iter (KA.clientStep l d) KA.stClient) (_ , KA.apiKAev l d sendKADone) U.tt
decKAc-src l d (kcSil st)  = SrcOpK.iter-bind (SrcOpK.Ret (inj₁ st)) (KA.clientStep l d)
-- errCookie terminal: the succV-successor of `kcErr1` along the errCookie emit is
-- `iter-bind (Ret (inj₂ _)) clientStep` (defeq `iter clientStep stDone`), forces to `ret`
decKAc-src l d kcTermE1    = SrcOpK.iter-bind (SrcOpK.Ret (inj₂ _)) (KA.clientStep l d)

-- the fine KeepAlive-server position
data KAsPos : Set where
  ksHead  : KA.KAState → KAsPos   -- loop head `iter (serverStep) st`
  ksRecv1 : Cookie → KAsPos       -- stClient recv MsgKeepAlive c: offers `apiKAev recvKACookie! c` → ksSil (stServer c) (io-case post-receive leaf)
  ksDdone1 : KAsPos               -- stClient recv MsgKADone: offers `doneKA` → ksSil stDone (io-case post-receive done leaf)
  ksSil   : KA.KAState → KAsPos   -- loop re-entry `iter-bind (Ret (inj₁ st)) (serverStep)`

-- source-side decode of the KeepAlive server peer at a fine position
decKAs-src : Link → Dir → KAsPos → KAProc
decKAs-src l d (ksHead st)   = SrcOpK.iter (KA.serverStep l d) st
decKAs-src l d (ksRecv1 c)   =
  succVK (SrcOpK.iter (KA.serverStep l d) KA.stClient) (_ , KA.receiveKA l d)
         (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))
decKAs-src l d ksDdone1      =
  succVK (SrcOpK.iter (KA.serverStep l d) KA.stClient) (_ , KA.receiveKA l d)
         (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)
decKAs-src l d (ksSil st)    = SrcOpK.iter-bind (SrcOpK.Ret (inj₁ st)) (KA.serverStep l d)

------------------------------------------------------------------------
-- LeiosNotify / LeiosFetch CLIENT / SERVER positions (R2 D3, LN/LF uniformity
-- pass).  Both pairs are FROZEN undriven at their loop head (the client offers
-- only the undriven `apiLNev`/`apiLFev`; the server offers only the wire
-- `receiveLN`/`receiveLF` that the client never sends), so the reachable-when-
-- undriven position is the loop head.  Mirroring KA/TS, a `…Head`/`…Sil` pair
-- over the state enum captures the head + the loop re-entry sil (the latter is
-- a target of the deferred io co-move; it carries the genuine loop-τ that
-- `bundle-τ-inv` routes).  Unlike KA, LN/LF are NOT on the abstract side
-- (`specBundle` is 8-peer KA/CS/BF/TS), so no coarsen/abstract decode is needed.
------------------------------------------------------------------------

-- the fine LeiosNotify-client position
data LNcPos : Set where
  lncHead : LN.LNState → LNcPos   -- loop head `iter (clientStep) st`
  lncRann1 : Header → LNcPos      -- stBusy recv MsgLNBlockAnnouncement h: offers `apiLNev recvLNBlockAnnouncement! h` → lncSil stIdle (io-case post-receive leaf)
  lncRoff1 : Point → LNcPos       -- stBusy recv MsgLNBlockOffer q: offers `apiLNev recvLNBlockOffer! q` → lncSil stIdle
  lncRtxs1 : Point → LNcPos       -- stBusy recv MsgLNBlockTxsOffer q: offers `apiLNev recvLNBlockTxsOffer! q` → lncSil stIdle
  lncRvot1 : List Vote → LNcPos   -- stBusy recv MsgLNVotesOffer vs: offers `apiLNev recvLNVotesOffer! vs` (Output) → lncSil stIdle
  lncReq1 : LNcPos                -- stIdle post-apiLNev sendLNRequestNext: offers `sendLN!` (MsgLNRequestNext) → lncSil stBusy (io-case send leaf)
  lncDone1 : LNcPos               -- stIdle post-apiLNev sendLNDone: offers `sendLN!` (MsgLNDone) → lncSil stDone (io-case send leaf)
  lncSil  : LN.LNState → LNcPos   -- loop re-entry `iter-bind (Ret (inj₁ st)) (clientStep)`

-- source-side decode of the LeiosNotify client peer at a fine position
decLNc-src : Link → Dir → LNcPos → LNProc
decLNc-src l d (lncHead st) = SrcOpN.iter (LN.clientStep l d) st
decLNc-src l d (lncRann1 h) =
  succVN (SrcOpN.iter (LN.clientStep l d) LN.stBusy) (_ , LN.receiveLN l d)
         (time₀ , FromInitiator , length₀ , leiosNotify (MsgLNBlockAnnouncement h))
decLNc-src l d (lncRoff1 q) =
  succVN (SrcOpN.iter (LN.clientStep l d) LN.stBusy) (_ , LN.receiveLN l d)
         (time₀ , FromInitiator , length₀ , leiosNotify (MsgLNBlockOffer q))
decLNc-src l d (lncRtxs1 q) =
  succVN (SrcOpN.iter (LN.clientStep l d) LN.stBusy) (_ , LN.receiveLN l d)
         (time₀ , FromInitiator , length₀ , leiosNotify (MsgLNBlockTxsOffer q))
decLNc-src l d (lncRvot1 vs) =
  succVN (SrcOpN.iter (LN.clientStep l d) LN.stBusy) (_ , LN.receiveLN l d)
         (time₀ , FromInitiator , length₀ , leiosNotify (MsgLNVotesOffer vs))
decLNc-src l d lncReq1  =
  succVN (SrcOpN.iter (LN.clientStep l d) LN.stIdle) (_ , LN.apiLNev l d sendLNRequestNext) U.tt
decLNc-src l d lncDone1 =
  succVN (SrcOpN.iter (LN.clientStep l d) LN.stIdle) (_ , LN.apiLNev l d sendLNDone) U.tt
decLNc-src l d (lncSil st)  = SrcOpN.iter-bind (SrcOpN.Ret (inj₁ st)) (LN.clientStep l d)

-- the fine LeiosNotify-server position
data LNsPos : Set where
  lnsHead  : LN.LNState → LNsPos   -- loop head `iter (serverStep) st`
  lnsDone1 : LNsPos                -- stIdle recv MsgLNDone: offers `doneLN` → lnsSil stDone (io-case post-receive done leaf)
  lnsWann1 : Header → LNsPos       -- stBusy post-apiLNev sendLNBlockAnnouncement h: offers `sendLN!` (MsgLNBlockAnnouncement h) → lnsSil stIdle (io-case send leaf)
  lnsWoff1 : Point → LNsPos        -- stBusy post-apiLNev sendLNBlockOffer q: offers `sendLN!` (MsgLNBlockOffer q) → lnsSil stIdle
  lnsWtxs1 : Point → LNsPos        -- stBusy post-apiLNev sendLNBlockTxsOffer q: offers `sendLN!` (MsgLNBlockTxsOffer q) → lnsSil stIdle
  lnsWvot1 : List Vote → LNsPos    -- stBusy post-apiLNev sendLNVotesOffer vs: offers `sendLN!` (MsgLNVotesOffer vs) → lnsSil stIdle
  lnsSil   : LN.LNState → LNsPos   -- loop re-entry `iter-bind (Ret (inj₁ st)) (serverStep)`

-- source-side decode of the LeiosNotify server peer at a fine position
decLNs-src : Link → Dir → LNsPos → LNProc
decLNs-src l d (lnsHead st)  = SrcOpN.iter (LN.serverStep l d) st
decLNs-src l d lnsDone1      =
  succVN (SrcOpN.iter (LN.serverStep l d) LN.stIdle) (_ , LN.receiveLN l d)
         (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone)
decLNs-src l d (lnsWann1 h) =
  succVN (SrcOpN.iter (LN.serverStep l d) LN.stBusy) (_ , LN.apiLNev l d sendLNBlockAnnouncement) h
decLNs-src l d (lnsWoff1 q) =
  succVN (SrcOpN.iter (LN.serverStep l d) LN.stBusy) (_ , LN.apiLNev l d sendLNBlockOffer) q
decLNs-src l d (lnsWtxs1 q) =
  succVN (SrcOpN.iter (LN.serverStep l d) LN.stBusy) (_ , LN.apiLNev l d sendLNBlockTxsOffer) q
decLNs-src l d (lnsWvot1 vs) =
  succVN (SrcOpN.iter (LN.serverStep l d) LN.stBusy) (_ , LN.apiLNev l d sendLNVotesOffer) vs
decLNs-src l d (lnsSil st)   = SrcOpN.iter-bind (SrcOpN.Ret (inj₁ st)) (LN.serverStep l d)

-- the fine LeiosFetch-client position
data LFcPos : Set where
  lfcHead : LF.LFState → LFcPos       -- loop head `iter (clientStep) st`
  lfcRblk1  : Block → LFcPos          -- stBlock recv MsgLFBlock b: offers `apiLFev recvLFBlock! b` → lfcSil stIdle
  lfcRbtx1  : List Tx → LFcPos        -- stBlockTxs recv MsgLFBlockTxs ts: offers `apiLFev recvLFBlockTxs! ts` (Output) → lfcSil stIdle
  lfcRvot1  : List VoteBlob → LFcPos  -- stVotes recv MsgLFVoteDelivery vs: offers `apiLFev recvLFVoteDelivery! vs` (Output) → lfcSil stIdle
  lfcRnext1 : Block → List Tx → LFcPos -- stBlockRange recv MsgLFNextBlockAndTxsInRange b ts: offers `apiLFev recvLFRangeBlock! (b,ts)` (Output) → lfcSil stBlockRange (loop)
  lfcRlast1 : Block → List Tx → LFcPos -- stBlockRange recv MsgLFLastBlockAndTxsInRange b ts: offers `apiLFev recvLFRangeBlock! (b,ts)` (Output) → lfcSil stIdle (final)
  lfcWblk1 : Point → LFcPos           -- stIdle post-apiLFev sendLFBlockRequest pt: offers `sendLF!` (MsgLFBlockRequest pt) → lfcSil stBlock (io-case send leaf)
  lfcWtxs1 : Point × LFBitmap → LFcPos -- stIdle post-apiLFev sendLFBlockTxsRequest (pt,bm): offers `sendLF!` (MsgLFBlockTxsRequest pt bm) → lfcSil stBlockTxs
  lfcWvot1 : List Vote → LFcPos       -- stIdle post-apiLFev sendLFVotesRequest vs: offers `sendLF!` (MsgLFVotesRequest vs) → lfcSil stVotes
  lfcWrng1 : ChainRange → LFcPos      -- stIdle post-apiLFev sendLFBlockRangeRequest r: offers `sendLF!` (MsgLFBlockRangeRequest r) → lfcSil stBlockRange
  lfcDone1 : LFcPos                   -- stIdle post-apiLFev sendLFDone: offers `sendLF!` (MsgLFDone) → lfcSil stDone
  lfcSil  : LF.LFState → LFcPos       -- loop re-entry `iter-bind (Ret (inj₁ st)) (clientStep)`

-- source-side decode of the LeiosFetch client peer at a fine position
decLFc-src : Link → Dir → LFcPos → LFProc
decLFc-src l d (lfcHead st) = SrcOpF.iter (LF.clientStep l d) st
decLFc-src l d (lfcRblk1 b)     =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stBlock) (_ , LF.receiveLF l d)
         (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlock b))
decLFc-src l d (lfcRbtx1 ts)    =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stBlockTxs) (_ , LF.receiveLF l d)
         (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxs ts))
decLFc-src l d (lfcRvot1 vs)    =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stVotes) (_ , LF.receiveLF l d)
         (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVoteDelivery vs))
decLFc-src l d (lfcRnext1 b ts) =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stBlockRange) (_ , LF.receiveLF l d)
         (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts))
decLFc-src l d (lfcRlast1 b ts) =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stBlockRange) (_ , LF.receiveLF l d)
         (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts))
decLFc-src l d (lfcWblk1 pt) =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stIdle) (_ , LF.apiLFev l d sendLFBlockRequest) pt
decLFc-src l d (lfcWtxs1 pb) =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stIdle) (_ , LF.apiLFev l d sendLFBlockTxsRequest) pb
decLFc-src l d (lfcWvot1 vs) =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stIdle) (_ , LF.apiLFev l d sendLFVotesRequest) vs
decLFc-src l d (lfcWrng1 r) =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stIdle) (_ , LF.apiLFev l d sendLFBlockRangeRequest) r
decLFc-src l d lfcDone1 =
  succVF (SrcOpF.iter (LF.clientStep l d) LF.stIdle) (_ , LF.apiLFev l d sendLFDone) U.tt
decLFc-src l d (lfcSil st)  = SrcOpF.iter-bind (SrcOpF.Ret (inj₁ st)) (LF.clientStep l d)

-- the fine LeiosFetch-server position
data LFsPos : Set where
  lfsHead  : LF.LFState → LFsPos   -- loop head `iter (serverStep) st`
  lfsDone1 : LFsPos                -- stIdle recv MsgLFDone: offers `doneLF` → lfsSil stDone (io-case post-receive done leaf)
  lfsWblk1 : Block → LFsPos        -- stBlock post-apiLFev sendLFBlock b: offers `sendLF!` (MsgLFBlock b) → lfsSil stIdle (io-case send leaf)
  lfsWtxs1 : List Tx → LFsPos      -- stBlockTxs post-apiLFev sendLFBlockTxs ts: offers `sendLF!` (MsgLFBlockTxs ts) → lfsSil stIdle
  lfsWvot1 : List VoteBlob → LFsPos -- stVotes post-apiLFev sendLFVoteDelivery vs: offers `sendLF!` (MsgLFVoteDelivery vs) → lfsSil stIdle
  lfsWnext1 : Block × List Tx → LFsPos -- stBlockRange post-apiLFev sendLFNextBlockAndTxsInRange (b,ts): offers `sendLF!` → lfsSil stBlockRange (loop)
  lfsWlast1 : Block × List Tx → LFsPos -- stBlockRange post-apiLFev sendLFLastBlockAndTxsInRange (b,ts): offers `sendLF!` → lfsSil stIdle (final)
  lfsSil   : LF.LFState → LFsPos   -- loop re-entry `iter-bind (Ret (inj₁ st)) (serverStep)`

-- source-side decode of the LeiosFetch server peer at a fine position
decLFs-src : Link → Dir → LFsPos → LFProc
decLFs-src l d (lfsHead st)  = SrcOpF.iter (LF.serverStep l d) st
decLFs-src l d lfsDone1      =
  succVF (SrcOpF.iter (LF.serverStep l d) LF.stIdle) (_ , LF.receiveLF l d)
         (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone)
decLFs-src l d (lfsWblk1 b) =
  succVF (SrcOpF.iter (LF.serverStep l d) LF.stBlock) (_ , LF.apiLFev l d sendLFBlock) b
decLFs-src l d (lfsWtxs1 ts) =
  succVF (SrcOpF.iter (LF.serverStep l d) LF.stBlockTxs) (_ , LF.apiLFev l d sendLFBlockTxs) ts
decLFs-src l d (lfsWvot1 vs) =
  succVF (SrcOpF.iter (LF.serverStep l d) LF.stVotes) (_ , LF.apiLFev l d sendLFVoteDelivery) vs
decLFs-src l d (lfsWnext1 bt) =
  succVF (SrcOpF.iter (LF.serverStep l d) LF.stBlockRange) (_ , LF.apiLFev l d sendLFNextBlockAndTxsInRange) bt
decLFs-src l d (lfsWlast1 bt) =
  succVF (SrcOpF.iter (LF.serverStep l d) LF.stBlockRange) (_ , LF.apiLFev l d sendLFLastBlockAndTxsInRange) bt
decLFs-src l d (lfsSil st)   = SrcOpF.iter-bind (SrcOpF.Ret (inj₁ st)) (LF.serverStep l d)

------------------------------------------------------------------------
-- The four fine peer decoders: rename the source-side derivative into the
-- whole-system `Net_Api` alphabet.  At `csHead stIdle` (resp. `ssHead`/
-- `bcHead`/`bsHead stIdle`) this is definitionally the NetworkPar builder
-- (`CSclientA l d` etc.), so the node home-equalities stay `refl`.
------------------------------------------------------------------------

-- decode the ChainSync client peer on `(l, d)` at fine position `pos`
decCSc : Link → Dir → CScPos → NetProc
decCSc l d pos = RenCS.renameMap (decCSc-src l d pos)

-- decode the ChainSync server peer on `(l, d)` at fine position `pos`
decCSs : Link → Dir → CSsPos → NetProc
decCSs l d pos = RenCS.renameMap (decCSs-src l d pos)

-- decode the BlockFetch client peer on `(l, d)` at fine position `pos`
decBFc : Link → Dir → BFcPos → NetProc
decBFc l d pos = RenBF.renameMap (decBFc-src l d pos)

-- decode the BlockFetch server peer on `(l, d)` at fine position `pos`
decBFs : Link → Dir → BFsPos → NetProc
decBFs l d pos = RenBF.renameMap (decBFs-src l d pos)

-- decode the TxSubmission client peer on `(l, d)` at fine position `pos`
-- (at `tcHead stInit` this is definitionally `TSclientA l d`, so home stays refl)
decTSc : Link → Dir → TScPos → NetProc
decTSc l d pos = RenTS.renameMap (decTSc-src l d pos)

-- decode the TxSubmission server peer on `(l, d)` at fine position `pos`
-- (at `tsHead stInit` this is definitionally `TSserverA l d`, so home stays refl)
decTSs : Link → Dir → TSsPos → NetProc
decTSs l d pos = RenTS.renameMap (decTSs-src l d pos)

-- decode the KeepAlive client peer on `(l, d)` at fine position `pos`
-- (at `kcHead stClient` this is definitionally `KAclientA l d`, so home stays refl)
decKAc : Link → Dir → KAcPos → NetProc
decKAc l d pos = RenKA.renameMap (decKAc-src l d pos)

-- decode the KeepAlive server peer on `(l, d)` at fine position `pos`
-- (at `ksHead stClient` this is definitionally `KAserverA l d`, so home stays refl)
decKAs : Link → Dir → KAsPos → NetProc
decKAs l d pos = RenKA.renameMap (decKAs-src l d pos)

-- decode the LeiosNotify client peer on `(l, d)` at fine position `pos`
-- (at `lncHead stIdle` this is definitionally `LNclientA l d`, so home stays refl)
decLNc : Link → Dir → LNcPos → NetProc
decLNc l d pos = RenLN.renameMap (decLNc-src l d pos)

-- decode the LeiosNotify server peer on `(l, d)` at fine position `pos`
-- (at `lnsHead stIdle` this is definitionally `LNserverA l d`, so home stays refl)
decLNs : Link → Dir → LNsPos → NetProc
decLNs l d pos = RenLN.renameMap (decLNs-src l d pos)

-- decode the LeiosFetch client peer on `(l, d)` at fine position `pos`
-- (at `lfcHead stIdle` this is definitionally `LFclientA l d`, so home stays refl)
decLFc : Link → Dir → LFcPos → NetProc
decLFc l d pos = RenLF.renameMap (decLFc-src l d pos)

-- decode the LeiosFetch server peer on `(l, d)` at fine position `pos`
-- (at `lfsHead stIdle` this is definitionally `LFserverA l d`, so home stays refl)
decLFs : Link → Dir → LFsPos → NetProc
decLFs l d pos = RenLF.renameMap (decLFs-src l d pos)

-- the tracked position of the (otherwise inert) TxSubmission / KeepAlive /
-- LeiosNotify / LeiosFetch peers on one link.  ONE record per link bundles all
-- eight inert peer positions (CS/BF are the driven peers, tracked separately)
record InertPos : Set where
  constructor mkInert
  field
    tsc : TScPos       -- TxSubmission client position
    tss : TSsPos       -- TxSubmission server position
    kac : KAcPos       -- KeepAlive client position
    kas : KAsPos       -- KeepAlive server position
    lnc : LNcPos       -- LeiosNotify client position
    lns : LNsPos       -- LeiosNotify server position
    lfc : LFcPos       -- LeiosFetch client position
    lfs : LFsPos       -- LeiosFetch server position
open InertPos public

-- the initial inert position: TS peers at loop-head init, KA peers at loop-head
-- client, LN/LF peers at their loop-head idle state (their frozen undriven heads)
initInert : InertPos
initInert = mkInert (tcHead TS.stInit) (tsHead TS.stInit) (kcHead KA.stClient) (ksHead KA.stClient)
                    (lncHead LN.stIdle) (lnsHead LN.stIdle) (lfcHead LF.stIdle) (lfsHead LF.stIdle)

------------------------------------------------------------------------
-- Producer-driver decode: `produce l d blkA` is a straight prefix chain of
-- nine api events (the trailing two are the `done` receipt callbacks synced with
-- the CS and BF servers); its position is the number of events already fired
-- (`pp0` = the whole body, `pp7` = the ChainSync `done`-receipt offer, `pp8` =
-- the BlockFetch `done`-receipt offer, `pp9` = the trailing `Skip`).
-- Each non-init phase is the genuine derivative — the literal chain tail.
------------------------------------------------------------------------

-- the `produce` driver phase (events fired so far, 0..9)
data ProdPh : Set where
  pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 : ProdPh

-- decode the `produce l d blk` driver at phase `ph` (the block `blk` is now a
-- parameter — nodeA passes `blkA`; relay nodes B/C pass their consumed block)
decProd : Link → Dir → Block₃ → ProdPh → NetProc
decProd l d blk pp0 = produce l d blk
decProd l d blk pp1 =
  apiCS l d sendCSAwaitReply ⟶₀
  (apiCS l d sendCSRollForward ! (header blk , tip blk) ⟶
  (apiBF l d reqBFRange ⟶ (λ _ →
  (apiBF l d sendBFStartBatch ! U.tt ⟶
  (apiBF l d sendBFBlock ! blk ⟶
  (apiBF l d sendBFBatchDone ! U.tt ⟶ (done l d N2N_ChainSync ⟶₀ (done l d N2N_BlockFetch ⟶₀ Skip))))))))
decProd l d blk pp2 =
  apiCS l d sendCSRollForward ! (header blk , tip blk) ⟶
  (apiBF l d reqBFRange ⟶ (λ _ →
  (apiBF l d sendBFStartBatch ! U.tt ⟶
  (apiBF l d sendBFBlock ! blk ⟶
  (apiBF l d sendBFBatchDone ! U.tt ⟶ (done l d N2N_ChainSync ⟶₀ (done l d N2N_BlockFetch ⟶₀ Skip)))))))
decProd l d blk pp3 =
  apiBF l d reqBFRange ⟶ (λ _ →
  (apiBF l d sendBFStartBatch ! U.tt ⟶
  (apiBF l d sendBFBlock ! blk ⟶
  (apiBF l d sendBFBatchDone ! U.tt ⟶ (done l d N2N_ChainSync ⟶₀ (done l d N2N_BlockFetch ⟶₀ Skip))))))
decProd l d blk pp4 =
  apiBF l d sendBFStartBatch ! U.tt ⟶
  (apiBF l d sendBFBlock ! blk ⟶
  (apiBF l d sendBFBatchDone ! U.tt ⟶ (done l d N2N_ChainSync ⟶₀ (done l d N2N_BlockFetch ⟶₀ Skip))))
decProd l d blk pp5 =
  apiBF l d sendBFBlock ! blk ⟶
  (apiBF l d sendBFBatchDone ! U.tt ⟶ (done l d N2N_ChainSync ⟶₀ (done l d N2N_BlockFetch ⟶₀ Skip)))
decProd l d blk pp6 =
  apiBF l d sendBFBatchDone ! U.tt ⟶ (done l d N2N_ChainSync ⟶₀ (done l d N2N_BlockFetch ⟶₀ Skip))
decProd l d blk pp7 = done l d N2N_ChainSync ⟶₀ (done l d N2N_BlockFetch ⟶₀ Skip)
decProd l d blk pp8 = done l d N2N_BlockFetch ⟶₀ Skip
decProd l d blk pp9 = Skip

------------------------------------------------------------------------
-- The node-A abstract state and its decode.
------------------------------------------------------------------------

-- the joint abstract position of node A: per link (AB, AC) the four driven
-- CS/BF peer FSM positions + the `produce` driver phase.  The eight inert
-- peers (KA/TS/LN/LF client+server) contribute no component.
record NodeStateA : Set where
  constructor mkNodeA
  field
    -- link AB (miniProtocols linkAB lo hi: clients on lo, servers on hi)
    csC-AB  : CScPos       -- ChainSync client  (AB, lo)
    csS-AB  : CSsPos       -- ChainSync server  (AB, hi) — produce-driven
    bfC-AB  : BFcPos       -- BlockFetch client (AB, lo)
    bfS-AB  : BFsPos       -- BlockFetch server (AB, hi) — produce-driven
    prod-AB : ProdPh       -- produce linkAB hi blkA phase
    -- link AC
    csC-AC  : CScPos
    csS-AC  : CSsPos
    bfC-AC  : BFcPos
    bfS-AC  : BFsPos
    prod-AC : ProdPh       -- produce linkAC hi blkA phase
    -- the tracked TxSubmission pair per link (KA/LN/LF stay constant)
    inert-AB : InertPos
    inert-AC : InertPos
open NodeStateA public

-- one link's twelve-peer bundle, INLINE in the exact `miniProtocols l lo hi`
-- interleave order (NetworkPar.435): KA c/s, then the driven CS c/s and BF c/s
-- at their fine positions, then the inert TS / LN / LF c/s literals.
bundleA : (l : Link) → CScPos → CSsPos → BFcPos → BFsPos → InertPos → NetProc
bundleA l csc css bfc bfs ip =
  decKAc l lo (kac ip) ⦀ (decKAs l hi (kas ip)
    ⦀ (decCSc l lo csc ⦀ (decCSs l hi css
    ⦀ (decBFc l lo bfc ⦀ (decBFs l hi bfs
    ⦀ (decTSc l lo (tsc ip) ⦀ (decTSs l hi (tss ip)
    ⦀ (decLNc l lo (lnc ip) ⦀ (decLNs l hi (lns ip)
    ⦀ (decLFc l lo (lfc ip) ⦀ decLFs l hi (lfs ip)))))))))))

-- the node-A decode: rebuild the two link bundles interleaved, synchronised
-- on `apiES` with the two produce drivers — the literal `nodeA` shape.
decNodeA : NodeStateA → NetProc
decNodeA s =
  (bundleA linkAB (csC-AB s) (csS-AB s) (bfC-AB s) (bfS-AB s) (inert-AB s)
   ⦀ bundleA linkAC (csC-AC s) (csS-AC s) (bfC-AC s) (bfS-AC s) (inert-AC s))
    ∥⇘ apiES ⇙ (decProd linkAB hi blkA (prod-AB s) ⦀ decProd linkAC hi blkA (prod-AC s))

-- the initial node-A position: every peer at its loop-head idle position +
-- both produce drivers unstepped + both TS pairs at their init head
initNodeA : NodeStateA
initNodeA = mkNodeA (csHead CS.stIdle) (ssHead CS.stIdle) (bcHead BF.stIdle) (bsHead BF.stIdle) pp0
                    (csHead CS.stIdle) (ssHead CS.stIdle) (bcHead BF.stIdle) (bsHead BF.stIdle) pp0
                    initInert initInert

-- NODE-A home-equality, GENUINE and `refl`: at the initial position each CS/BF
-- peer decode is its NetworkPar builder (`renameMap (iter step stIdle)`) and
-- each `produce` decode is its whole body, so the inline bundle is
-- definitionally `miniProtocols linkAB lo hi ⦀ miniProtocols linkAC lo hi`
-- and the composite is `nodeA` — WITHOUT forcing the composite tree to WHNF.
decNodeA-home : decNodeA initNodeA ≡ nodeA blkA
decNodeA-home = refl

------------------------------------------------------------------------
-- TASK 3b — the other three nodes (B, C, D), mirroring 3a.
--
-- B and C are RELAY nodes (`consume … >>= produce …`); D is a pure CONSUMER
-- (`consume … >> Skip` on both its links).  The peer bundle is reconstructed
-- at the SAME coarse loop-head granularity as node A (`decCSc`/`…`/`decBFs`
-- from `iter step st`); the consume-side driver is a straight client chain
-- (mirror of `decProd`) and the produce leg of B/C REUSES `decProd`.
------------------------------------------------------------------------

-- one link's twelve-peer bundle for GENERAL client/server directions `(cl,sv)`
-- (node A fixes `cl=lo, sv=hi`; B/C/D need `hi/lo`, `lo/hi`, `hi/lo`).  INLINE
-- in the exact `miniProtocols l cl sv` interleave order (NetworkPar.435): the
-- four driven CS/BF peers at their positions, the eight inert KA/TS/LN/LF as
-- literal builders.  At all-`stIdle` this is definitionally `miniProtocols l cl sv`.
bundleG : (l : Link) (cl sv : Dir)
        → CScPos → CSsPos → BFcPos → BFsPos → InertPos → NetProc
bundleG l cl sv csc css bfc bfs ip =
  decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip)
    ⦀ (decCSc l cl csc ⦀ (decCSs l sv css
    ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
    ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip)
    ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
    ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))

------------------------------------------------------------------------
-- Consumer-driver decode: `consume l d` is a straight client chain of six api
-- events with two data-dependent tails (the `RollForward` header `b`, the
-- received block `b′`).  Its phase is the number of events already fired
-- (`cp0` = the whole body, `cp6` = the trailing `Ret`).  The `Block₃`
-- argument supplies the received block to the tails past `recvCSRollforward`.
------------------------------------------------------------------------

-- the `consume` driver phase (client-chain events fired so far, 0..6)
data ConsPh : Set where
  cp0 cp1 cp2 cp3 cp4 cp5 cp6 : ConsPh

-- decode the `consume l d` client driver at phase `ph`; `b` feeds the
-- data-dependent tails (the block carried by `recvCSRollforward`/`recvBFBlock`)
decCons : Link → Dir → Block₃ → ConsPh
        → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃
decCons l d b cp0 = consume l d
decCons l d b cp1 =
  apiCS l d recvCSRollforward ⟶ consume-k l d
decCons l d b cp2 =
  apiBF l d sendBFRequestRange ! (chainRange (point b) (point b)) ⟶
  (apiBF l d recvBFBlock ⟶
  (λ b′ →
  (apiBF l d sendBFClientDone ! U.tt ⟶
  (apiCS l d sendCSDone ⟶₀
  Ret b′))))
decCons l d b cp3 =
  apiBF l d recvBFBlock ⟶
  (λ b′ →
  (apiBF l d sendBFClientDone ! U.tt ⟶
  (apiCS l d sendCSDone ⟶₀
  Ret b′)))
decCons l d b cp4 =
  apiBF l d sendBFClientDone ! U.tt ⟶
  (apiCS l d sendCSDone ⟶₀
  Ret b)
decCons l d b cp5 =
  apiCS l d sendCSDone ⟶₀
  Ret b
decCons l d b cp6 = Ret b

-- node-D consume-driver phase: the received/in-flight block `cblk` plus the
-- straight-chain phase `cph` (the block is a placeholder `blkA` until cp1/cp3
-- rebind it to the received value)
record ConsDPh : Set where
  constructor consD
  field
    cblk : Block₃
    cph  : ConsPh
open ConsDPh public

-- decode a node-D consume driver `consume l hi >> Skip` at phase `ph`, using
-- the stored block instead of a hardcoded `b1`
decConsD : Link → ConsDPh → NetProc
decConsD l (consD b ph) = decCons l hi b ph >> Skip

------------------------------------------------------------------------
-- The node-D abstract state and decode (pure consumer on links BD, CD).
------------------------------------------------------------------------

-- node D's joint position: per link (BD, CD) the four CS/BF peer FSM positions
-- (clients on hi, servers on lo) + that link's `consume … >> Skip` phase.
record NodeStateD : Set where
  constructor mkNodeD
  field
    -- link BD (miniProtocols linkBD hi lo: clients on hi, servers on lo)
    csC-BD  : CScPos
    csS-BD  : CSsPos
    bfC-BD  : BFcPos
    bfS-BD  : BFsPos
    cons-BD : ConsDPh      -- consume linkBD hi >> Skip phase (+ received block)
    -- link CD
    csC-CD  : CScPos
    csS-CD  : CSsPos
    bfC-CD  : BFcPos
    bfS-CD  : BFsPos
    cons-CD : ConsDPh      -- consume linkCD hi >> Skip phase (+ received block)
    -- the tracked TxSubmission pair per link
    inert-BD : InertPos
    inert-CD : InertPos
open NodeStateD public

-- the node-D decode: two link bundles interleaved, synchronised on `apiES`
-- with the two `consume … >> Skip` drivers — the literal `nodeD` shape.
decNodeD : NodeStateD → NetProc
decNodeD s =
  (bundleG linkBD hi lo (csC-BD s) (csS-BD s) (bfC-BD s) (bfS-BD s) (inert-BD s)
   ⦀ bundleG linkCD hi lo (csC-CD s) (csS-CD s) (bfC-CD s) (bfS-CD s) (inert-CD s))
    ∥⇘ apiES ⇙ (decConsD linkBD (cons-BD s) ⦀ decConsD linkCD (cons-CD s))

-- the initial node-D position: every peer at its loop-head idle position +
-- both consume drivers unstepped + both TS pairs at their init head
initNodeD : NodeStateD
initNodeD = mkNodeD (csHead CS.stIdle) (ssHead CS.stIdle) (bcHead BF.stIdle) (bsHead BF.stIdle) (consD blkA cp0)
                    (csHead CS.stIdle) (ssHead CS.stIdle) (bcHead BF.stIdle) (bsHead BF.stIdle) (consD blkA cp0)
                    initInert initInert

-- NODE-D home-equality, GENUINE and `refl`: at init each CS/BF peer decode is
-- its NetworkPar builder and each `consume … >> Skip` decode is its whole body,
-- so the inline reconstruction is definitionally `nodeD` — no WHNF forcing.
decNodeD-home : decNodeD initNodeD ≡ nodeD
decNodeD-home = refl

------------------------------------------------------------------------
-- Relay driver decode: `consume l₁ hi >>= λ b → produce l₂ hi b`.  Its phase
-- is either the consume stage (a `ConsPh`, with the produce leg still bound
-- under `>>=`) or the produce stage (a `ProdPh`, REUSING `decProd`; in this
-- scenario the relayed block is `blkA`, so `decProd` is the genuine leg).
------------------------------------------------------------------------

-- the consume-then-produce driver phase for a relay node (B, C); both arms
-- carry the block (consuming: the received/in-flight block; producing: the
-- consumed block being relayed onward)
data CPPh : Set where
  consuming : Block₃ → ConsPh → CPPh   -- still consuming (produce leg bound under >>=)
  producing : Block₃ → ProdPh → CPPh   -- consume done, now producing the consumed block

-- decode the `consume l₁ hi >>= λ b → produce l₂ hi b` relay driver at phase `ph`
decCP : Link → Link → CPPh → NetProc
decCP l₁ l₂ (consuming b cp) = decCons l₁ hi b cp >>= λ b′ → produce l₂ hi b′
decCP l₁ l₂ (producing b pp) = decProd l₂ hi b pp

------------------------------------------------------------------------
-- The node-B abstract state and decode (relay: consume AB, produce BD).
------------------------------------------------------------------------

-- node B's joint position: link AB peers (clients on hi, servers on lo), link
-- BD peers (clients on lo, servers on hi) + the consume-then-produce phase.
record NodeStateB : Set where
  constructor mkNodeB
  field
    -- link AB (miniProtocols linkAB hi lo: clients on hi, servers on lo)
    csC-AB  : CScPos
    csS-AB  : CSsPos
    bfC-AB  : BFcPos
    bfS-AB  : BFsPos
    -- link BD (miniProtocols linkBD lo hi: clients on lo, servers on hi)
    csC-BD  : CScPos
    csS-BD  : CSsPos
    bfC-BD  : BFcPos
    bfS-BD  : BFsPos
    cp-B    : CPPh         -- consume linkAB hi >>= produce linkBD hi phase
    -- the tracked TxSubmission pair per link
    inert-AB : InertPos
    inert-BD : InertPos
open NodeStateB public

-- the node-B decode: link-AB and link-BD bundles interleaved, synchronised on
-- `apiES` with the consume-then-produce relay driver — the literal `nodeB` shape.
decNodeB : NodeStateB → NetProc
decNodeB s =
  (bundleG linkAB hi lo (csC-AB s) (csS-AB s) (bfC-AB s) (bfS-AB s) (inert-AB s)
   ⦀ bundleG linkBD lo hi (csC-BD s) (csS-BD s) (bfC-BD s) (bfS-BD s) (inert-BD s))
    ∥⇘ apiES ⇙ decCP linkAB linkBD (cp-B s)

-- the initial node-B position: every peer at its loop-head idle position +
-- driver at consume-init + both TS pairs at their init head
initNodeB : NodeStateB
initNodeB = mkNodeB (csHead CS.stIdle) (ssHead CS.stIdle) (bcHead BF.stIdle) (bsHead BF.stIdle)
                    (csHead CS.stIdle) (ssHead CS.stIdle) (bcHead BF.stIdle) (bsHead BF.stIdle) (consuming blkA cp0)
                    initInert initInert

-- NODE-B home-equality, GENUINE and `refl`: at init the driver decode is
-- `decCons linkAB hi blkA cp0 >>= …` = `consume linkAB hi >>= λ b → produce linkBD hi b`
-- and each peer is its builder, so the reconstruction is definitionally `nodeB`.
decNodeB-home : decNodeB initNodeB ≡ nodeB
decNodeB-home = refl

------------------------------------------------------------------------
-- The node-C abstract state and decode (relay: consume AC, produce CD).
------------------------------------------------------------------------

-- node C's joint position: link AC peers (clients on hi, servers on lo), link
-- CD peers (clients on lo, servers on hi) + the consume-then-produce phase.
record NodeStateC : Set where
  constructor mkNodeC
  field
    -- link AC (miniProtocols linkAC hi lo: clients on hi, servers on lo)
    csC-AC  : CScPos
    csS-AC  : CSsPos
    bfC-AC  : BFcPos
    bfS-AC  : BFsPos
    -- link CD (miniProtocols linkCD lo hi: clients on lo, servers on hi)
    csC-CD  : CScPos
    csS-CD  : CSsPos
    bfC-CD  : BFcPos
    bfS-CD  : BFsPos
    cp-C    : CPPh         -- consume linkAC hi >>= produce linkCD hi phase
    -- the tracked TxSubmission pair per link
    inert-AC : InertPos
    inert-CD : InertPos
open NodeStateC public

-- the node-C decode: link-AC and link-CD bundles interleaved, synchronised on
-- `apiES` with the consume-then-produce relay driver — the literal `nodeC` shape.
decNodeC : NodeStateC → NetProc
decNodeC s =
  (bundleG linkAC hi lo (csC-AC s) (csS-AC s) (bfC-AC s) (bfS-AC s) (inert-AC s)
   ⦀ bundleG linkCD lo hi (csC-CD s) (csS-CD s) (bfC-CD s) (bfS-CD s) (inert-CD s))
    ∥⇘ apiES ⇙ decCP linkAC linkCD (cp-C s)

-- the initial node-C position: every peer at its loop-head idle position +
-- driver at consume-init + both TS pairs at their init head
initNodeC : NodeStateC
initNodeC = mkNodeC (csHead CS.stIdle) (ssHead CS.stIdle) (bcHead BF.stIdle) (bsHead BF.stIdle)
                    (csHead CS.stIdle) (ssHead CS.stIdle) (bcHead BF.stIdle) (bsHead BF.stIdle) (consuming blkA cp0)
                    initInert initInert

-- NODE-C home-equality, GENUINE and `refl`: mirror of node B on linkAC/linkCD.
decNodeC-home : decNodeC initNodeC ≡ nodeC
decNodeC-home = refl

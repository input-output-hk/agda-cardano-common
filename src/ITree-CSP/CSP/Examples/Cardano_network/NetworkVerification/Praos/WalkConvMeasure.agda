{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the CONCRETE τ-convergence measure `μτ` (WalkConv item (a)).
--
-- `WalkConv.absNoDiv` is the well-founded τ-convergence engine parameterised
-- over a measure `μτ : RState → ℕ` and a per-τ strict-decrease reflector
-- `τreflect`.  This module supplies the CONCRETE `μτ` (LIGHT — only the
-- data-level `SysReach`/`SysMedium`/`SysNode` records, no reflection cone) and
-- the two arithmetic decrease facts each abstract-τ class must exhibit.
--
-- SHAPE (settled in the R3 plan):
--     μτ  =  3 · (Σ over the four abstract node FSMs of remaining wire events)
--         +  (Σ over the medium cells of `cellWt`,  empty=0 full=1 draining=2).
--
-- The τ's counted are ABSTRACT τ's (`radec r = absDec (toSys r)`); the abstract
-- nodes are τ-free `tableSpec` FSMs, so the node summand only ranks WIRE io
-- events (no sil-loop cycling to worry about).  A wire io-sync advances exactly
-- one CS/BF peer by one wire event ⇒ its "remaining wire events" drops by ≥1 ⇒
-- `3·(…)` drops by ≥3, while the synced medium cell rises by exactly 1
-- (empty→full on an INPUT, full→draining on an OUTPUT) ⇒ net ≤ −2.  A medium-τ
-- drains one cell draining→empty (−2), nodes fixed ⇒ −2.  Both strictly ↓.
--
-- The `posWt` node budgets below are the "remaining wire events (upper bound)
-- in a pure τ-chain" for each concrete peer FSM position — a SEND position ranks
-- one above its post-send `…Sil`; a receiving `…Head` ranks one above the
-- post-recv api-offer leaf; api/await-blocked leaves rank 0 (τ-stuck: their next
-- move is a VISIBLE api the τ-chain cannot fire).  Drivers (`ProdPh`/`ConsPh`/
-- `CPPh`/`ConsDPh`) and inert peers advance only on VISIBLE api, so they are
-- constant across a τ-chain and contribute 0.  (Proving each io-sync realises
-- the −1 per-peer drop is the heavy `SysIoLink6` per-peer cone — WalkConv item
-- (c); this module fixes the measure + the class arithmetic it must satisfy.)
--
-- No postulates, holes, or `--allow-unsolved-metas`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using ( +-mono-≤; *-monoʳ-≤; ≤-refl; ≤-trans; +-suc; +-comm; +-assoc
        ; *-suc; n≤1+n; module ≤-Reasoning )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvMeasure (blkA : Block₃) where

------------------------------------------------------------------------
-- The reachable-config domain + the medium/node state records.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; lo; hi; IDs
        ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
        ; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; toSys )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( MedState; phase; CopyPhase; empty; full; draining )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( NodeStateA; NodeStateB; NodeStateC; NodeStateD
        ; CScPos; csHead; csReqNext1; csFindInt1; csDone1
        ; csRF1; csRB1; csIF1; csINF1; csSil
        ; CSsPos; ssHead; ssReqNext1; ssFindInt1; ssDone1
        ; ssRF1; ssRB1; ssAw1; ssIF1; ssINF1; ssSil
        ; BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
        ; BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil
        ; InertPos; tsc; tss; kac; kas; lnc; lns; lfc; lfs
        ; TScPos; tcHead; tcReqIdsB1; tcReqIdsNB1; tcReqTxs1
        ; tcRepB1; tcDone1; tcRepNB1; tcRepTxs1; tcSil
        ; TSsPos; tsHead; tsDone1; tsReqB1; tsReqNB1; tsReqTxs1; tsSil
        ; KAcPos; kcHead; kcErr1; kcReq1; kcDone1; kcSil; kcTermE1
        ; KAsPos; ksHead; ksRecv1; ksDdone1; ksSil
        ; LNcPos; lncHead; lncRann1; lncRoff1; lncRtxs1; lncRvot1
        ; lncReq1; lncDone1; lncSil
        ; LNsPos; lnsHead; lnsDone1; lnsWann1; lnsWoff1; lnsWtxs1; lnsWvot1; lnsSil
        ; LFcPos; lfcHead; lfcRblk1; lfcRbtx1; lfcRvot1; lfcRnext1; lfcRlast1
        ; lfcWblk1; lfcWtxs1; lfcWvot1; lfcWrng1; lfcDone1; lfcSil
        ; LFsPos; lfsHead; lfsDone1; lfsWblk1; lfsWtxs1; lfsWvot1
        ; lfsWnext1; lfsWlast1; lfsSil )

-- the inert-peer FSM state enums (for the per-position wire budgets)
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.KeepAlive    p as KA
import CSP.Examples.Cardano_network.LeiosNotify  p as LN
import CSP.Examples.Cardano_network.LeiosFetch   p as LF

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( linkAB; linkAC; linkBD; linkCD )
import CSP.Examples.Cardano_network.ChainSync  p as CS
import CSP.Examples.Cardano_network.BlockFetch p as BF

------------------------------------------------------------------------
-- MEDIUM summand — `cellWt` and the whole-medium cell sum `medWt`.
------------------------------------------------------------------------

-- one copy cell's weight: empty=0, full=1, draining=2 (the draining transient
-- is the post-`output` cell that still owes one loop-back τ)
cellWt : CopyPhase → ℕ
cellWt empty        = 0
cellWt (full _)     = 1
cellWt (draining _) = 2

-- sum of `cellWt` over the 12 `uniformCfg` cells of one link's phase-row
rowWt : (Dir → IDs → CopyPhase) → ℕ
rowWt ph = cellWt (ph lo N2N_KeepAlive)    + cellWt (ph hi N2N_KeepAlive)
         + cellWt (ph lo N2N_ChainSync)    + cellWt (ph hi N2N_ChainSync)
         + cellWt (ph lo N2N_BlockFetch)   + cellWt (ph hi N2N_BlockFetch)
         + cellWt (ph lo N2N_TxSubmission) + cellWt (ph hi N2N_TxSubmission)
         + cellWt (ph lo N2N_LeiosNotify)  + cellWt (ph hi N2N_LeiosNotify)
         + cellWt (ph lo N2N_LeiosFetch)   + cellWt (ph hi N2N_LeiosFetch)

-- whole-medium weight: sum of the four links' row weights (numLinks = 4)
medWt : MedState → ℕ
medWt m = rowWt (phase m linkAB) + rowWt (phase m linkAC)
        + rowWt (phase m linkBD) + rowWt (phase m linkCD)

------------------------------------------------------------------------
-- NODE summand — per-peer "remaining wire events" budgets.
------------------------------------------------------------------------

-- ChainSync CLIENT: post-request states rank by the reply they await
-- SOUNDNESS FIX (2026-08-03): `stCanAwait` MUST rank ABOVE `stMustReply`.
-- From `stCanAwait` the client can receive `MsgCSAwaitReply` (an io/output
-- event) which advances it to `csSil stMustReply` (`csc-hstep`, SIL5:848),
-- from which it still owes ONE more reply-receive.  So a `stCanAwait` config
-- can take TWO wire receives (AwaitReply then the reply) to reach its leaf,
-- whereas `stMustReply` owes exactly one.  Ranking both `1` made the
-- `stCanAwait --receiveCS AwaitReply--> stMustReply` io transition NON-strict
-- (1→1) — the io-sync node drop would be 0 and `μτ-io-dec` would fail.  Bump
-- `stCanAwait` to 2 (and its feeder `csReqNext1` to 3) so every CS-client io
-- transition strictly drops.
posWt-CScSt : CS.CSState → ℕ
posWt-CScSt CS.stIdle      = 0    -- offers api requests (τ-stuck)
posWt-CScSt CS.stCanAwait  = 2    -- may recv AwaitReply → stMustReply(1), then a reply
posWt-CScSt CS.stMustReply = 1    -- awaits exactly one reply-receive → leaf(0)
posWt-CScSt CS.stIntersect = 1
posWt-CScSt CS.stDone      = 0

posWt-CSc : CScPos → ℕ
posWt-CSc (csHead st)     = posWt-CScSt st
posWt-CSc (csSil  st)     = posWt-CScSt st   -- abstract-collapse: same as head
posWt-CSc csReqNext1      = 3                -- send RequestNext → csSil stCanAwait(2)
posWt-CSc (csFindInt1 _)  = 2                -- send FindIntersect → stIntersect(1)
posWt-CSc csDone1         = 1                -- send Done → stDone(0)
posWt-CSc (csRF1 _ _)     = 0                -- offers api recv (τ-stuck)
posWt-CSc (csRB1 _ _)     = 0
posWt-CSc (csIF1 _ _)     = 0
posWt-CSc (csINF1 _)      = 0

-- ChainSync SERVER: idle awaits a request (one recv); reply-send states rank
-- one above their post-send loop state
posWt-CSsSt : CS.CSState → ℕ
posWt-CSsSt CS.stIdle      = 1    -- awaits a request on the wire (one recv)
posWt-CSsSt CS.stCanAwait  = 0    -- offers api replies (τ-stuck)
posWt-CSsSt CS.stMustReply = 0
posWt-CSsSt CS.stIntersect = 0
posWt-CSsSt CS.stDone      = 0

posWt-CSs : CSsPos → ℕ
posWt-CSs (ssHead st)     = posWt-CSsSt st
posWt-CSs (ssSil  st)     = posWt-CSsSt st
posWt-CSs ssReqNext1      = 0     -- offers api req (τ-stuck)
posWt-CSs (ssFindInt1 _)  = 0
posWt-CSs ssDone1         = 0
posWt-CSs (ssRF1 _ _)     = 2     -- send RollForward → ssSil stIdle(1)
posWt-CSs (ssRB1 _ _)     = 2
posWt-CSs (ssIF1 _ _)     = 2
posWt-CSs (ssINF1 _)      = 2
posWt-CSs ssAw1           = 1     -- send AwaitReply → ssSil stMustReply(0)

-- BlockFetch CLIENT: busy awaits StartBatch then streams blocks
posWt-BFcSt : BF.BFState → ℕ
posWt-BFcSt BF.stIdle      = 0    -- offers api requests (τ-stuck)
posWt-BFcSt BF.stBusy      = 2    -- recv StartBatch → stStreaming(1)
posWt-BFcSt BF.stStreaming = 1    -- recv Block → api-offer leaf(0)
posWt-BFcSt BF.stDone      = 0

posWt-BFc : BFcPos → ℕ
posWt-BFc (bcHead st)  = posWt-BFcSt st
posWt-BFc (bcSil  st)  = posWt-BFcSt st
posWt-BFc (bcReq1 _)   = 3        -- send RequestRange → bcSil stBusy(2)
posWt-BFc bcDone1      = 1        -- send ClientDone → bcSil stDone(0)
posWt-BFc (bcBlk1 _)   = 0        -- offers api recvBFBlock (τ-stuck)

-- BlockFetch SERVER: idle awaits a request; the send states rank one above
posWt-BFsSt : BF.BFState → ℕ
posWt-BFsSt BF.stIdle      = 1    -- awaits a request on the wire (one recv)
posWt-BFsSt BF.stBusy      = 0    -- offers api StartBatch/NoBlocks (τ-stuck)
posWt-BFsSt BF.stStreaming = 0    -- offers api Block/BatchDone (τ-stuck)
posWt-BFsSt BF.stDone      = 0

posWt-BFs : BFsPos → ℕ
posWt-BFs (bsHead st)   = posWt-BFsSt st
posWt-BFs (bsSil  st)   = posWt-BFsSt st
posWt-BFs (bsReq1 _)    = 0       -- offers api reqBFRange (τ-stuck)
posWt-BFs bsDone1       = 0
posWt-BFs bsStart1      = 1       -- send StartBatch → bsSil stStreaming(0)
posWt-BFs bsNoBlk1      = 2       -- send NoBlocks → bsSil stIdle(1)
posWt-BFs (bsBlk1 _)    = 1       -- send Block → bsSil stStreaming(0)
posWt-BFs bsBatchDone1  = 2       -- send BatchDone → bsSil stIdle(1)

------------------------------------------------------------------------
-- INERT-peer budgets — FULL per-position wire counts (R3 decision (B)).
--
-- Under decision (B) every inert peer (KA/LN/LF/TS, client + server) is
-- budgeted EXACTLY like the CS/BF peers: `posWt-Xc/Xs pos` = the number of
-- remaining WIRE events (`sendX!` / wire receive) fireable from `pos` before
-- the FSM next reaches an api-gated position (a state whose only enabled move
-- is a VISIBLE api the τ-chain cannot fire).  Every hidden io-sync advances the
-- fired peer through exactly ONE wire event ⇒ its budget drops by ≥1 ⇒ the
-- `nodesWt` summand drops by ≥1 ⇒ `3·(…)` drops ≥3, dominating the +1 medium
-- cell rise (net ≤ −2).  This makes EVERY inert io-sync drop `μτ`
-- UNCONDITIONALLY — no reachability invariant is needed (the abstract KA/LN/LF
-- peers never in fact fire io, since no driver emits their api, but the budget
-- discharges the drop even for the counterfactual).
--
-- The io transitions were read from the concrete FSMs (`KeepAlive`/
-- `LeiosNotify`/`LeiosFetch`/`TxSubmission` `clientStep`/`serverStep`):
--   * a SEND position (post-api `…W…1`/`…Req…1`/`…Rep…1`/`kcReq1`/… ) fires one
--     `sendX!` then lands one budget below its post-send `…Sil st`;
--   * a receiving loop head (`…Head st` at a state that receives a wire msg)
--     fires one wire receive then lands one budget below its post-recv position
--     (an api-offer leaf, a `…Done1`, or a directly-returned `…Sil st`);
--   * an api-gated head / api-offer receive-leaf owes no wire event ⇒ budget 0.
------------------------------------------------------------------------

-- KeepAlive CLIENT: at `stClient` offers api (send req/done, no io directly);
-- at `stServer c` receives the echoed cookie (one wire recv → stClient/error).
posWt-KAcSt : KA.KAState → ℕ
posWt-KAcSt KA.stClient     = 0    -- offers api sendKAMsg/sendKADone (τ-stuck)
posWt-KAcSt (KA.stServer _) = 1    -- recv MsgKeepAliveResponse → stClient(0)/kcErr1(0)
posWt-KAcSt KA.stDone       = 0

posWt-KAc : KAcPos → ℕ
posWt-KAc (kcHead st) = posWt-KAcSt st
posWt-KAc (kcSil  st) = posWt-KAcSt st
posWt-KAc (kcReq1 _)  = 2           -- send MsgKeepAlive → kcSil (stServer)(1)
posWt-KAc kcDone1     = 1           -- send MsgKADone → kcSil stDone(0)
posWt-KAc (kcErr1 _ _ _) = 0        -- offers api errCookie (τ-stuck)
posWt-KAc kcTermE1    = 0           -- √ terminal

-- KeepAlive SERVER: at `stClient` receives a request (one recv); at `stServer c`
-- sends the echoed response (one wire send → stClient).
posWt-KAsSt : KA.KAState → ℕ
posWt-KAsSt KA.stClient     = 1    -- recv MsgKeepAlive → ksRecv1(0) / MsgKADone → ksDdone1(0)
posWt-KAsSt (KA.stServer _) = 2    -- send MsgKeepAliveResponse → ksSil stClient(1)
posWt-KAsSt KA.stDone       = 0

posWt-KAs : KAsPos → ℕ
posWt-KAs (ksHead st) = posWt-KAsSt st
posWt-KAs (ksSil  st) = posWt-KAsSt st
posWt-KAs (ksRecv1 _) = 0           -- offers api recvKACookie! (τ-stuck)
posWt-KAs ksDdone1    = 0           -- offers doneKA (τ-stuck)

-- LeiosNotify CLIENT: at `stIdle` offers api requests (no io directly); at
-- `stBusy` receives one notification (one wire recv → api-offer leaf).
posWt-LNcSt : LN.LNState → ℕ
posWt-LNcSt LN.stIdle = 0           -- offers api sendLNRequestNext/sendLNDone (τ-stuck)
posWt-LNcSt LN.stBusy = 1           -- recv a notification → lncR*1(0)
posWt-LNcSt LN.stDone = 0

posWt-LNc : LNcPos → ℕ
posWt-LNc (lncHead st) = posWt-LNcSt st
posWt-LNc (lncSil  st) = posWt-LNcSt st
posWt-LNc (lncRann1 _) = 0          -- offers api recvLNBlockAnnouncement! (τ-stuck)
posWt-LNc (lncRoff1 _) = 0
posWt-LNc (lncRtxs1 _) = 0
posWt-LNc (lncRvot1 _) = 0
posWt-LNc lncReq1      = 2          -- send MsgLNRequestNext → lncSil stBusy(1)
posWt-LNc lncDone1     = 1          -- send MsgLNDone → lncSil stDone(0)

-- LeiosNotify SERVER: at `stIdle` receives a request/done (one recv → stBusy/done);
-- at `stBusy` sends one notification (one wire send → stIdle).
posWt-LNsSt : LN.LNState → ℕ
posWt-LNsSt LN.stIdle = 1           -- recv MsgLNRequestNext → stBusy(0) / MsgLNDone → lnsDone1(0)
posWt-LNsSt LN.stBusy = 0           -- offers api sendLNBlock…/Votes… (τ-stuck)
posWt-LNsSt LN.stDone = 0

posWt-LNs : LNsPos → ℕ
posWt-LNs (lnsHead st) = posWt-LNsSt st
posWt-LNs (lnsSil  st) = posWt-LNsSt st
posWt-LNs lnsDone1     = 0          -- offers doneLN (τ-stuck)
posWt-LNs (lnsWann1 _) = 2          -- send a notification → lnsSil stIdle(1)
posWt-LNs (lnsWoff1 _) = 2
posWt-LNs (lnsWtxs1 _) = 2
posWt-LNs (lnsWvot1 _) = 2

-- LeiosFetch CLIENT: at `stIdle` offers api requests (no io directly); at the
-- delivery states receives one payload (one wire recv → api-offer leaf).
posWt-LFcSt : LF.LFState → ℕ
posWt-LFcSt LF.stIdle       = 0     -- offers api send-requests (τ-stuck)
posWt-LFcSt LF.stBlock      = 1     -- recv MsgLFBlock → lfcRblk1(0)
posWt-LFcSt LF.stBlockTxs   = 1     -- recv MsgLFBlockTxs → lfcRbtx1(0)
posWt-LFcSt LF.stVotes      = 1     -- recv MsgLFVoteDelivery → lfcRvot1(0)
posWt-LFcSt LF.stBlockRange = 1     -- recv MsgLFNext/Last → lfcRnext1(0)/lfcRlast1(0)
posWt-LFcSt LF.stDone       = 0

posWt-LFc : LFcPos → ℕ
posWt-LFc (lfcHead st)    = posWt-LFcSt st
posWt-LFc (lfcSil  st)    = posWt-LFcSt st
posWt-LFc (lfcRblk1 _)    = 0       -- offers api recvLFBlock! (τ-stuck)
posWt-LFc (lfcRbtx1 _)    = 0
posWt-LFc (lfcRvot1 _)    = 0
posWt-LFc (lfcRnext1 _ _) = 0
posWt-LFc (lfcRlast1 _ _) = 0
posWt-LFc (lfcWblk1 _)    = 2       -- send MsgLFBlockRequest → lfcSil stBlock(1)
posWt-LFc (lfcWtxs1 _)    = 2       -- send MsgLFBlockTxsRequest → lfcSil stBlockTxs(1)
posWt-LFc (lfcWvot1 _)    = 2       -- send MsgLFVotesRequest → lfcSil stVotes(1)
posWt-LFc (lfcWrng1 _)    = 2       -- send MsgLFBlockRangeRequest → lfcSil stBlockRange(1)
posWt-LFc lfcDone1        = 1       -- send MsgLFDone → lfcSil stDone(0)

-- LeiosFetch SERVER: at `stIdle` receives a request (one recv → delivery
-- state/done); at each delivery state sends one payload (one wire send → stIdle).
posWt-LFsSt : LF.LFState → ℕ
posWt-LFsSt LF.stIdle       = 1     -- recv a request → stBlock/…/stBlockRange(0) or lfsDone1(0)
posWt-LFsSt LF.stBlock      = 0     -- offers api sendLFBlock (τ-stuck)
posWt-LFsSt LF.stBlockTxs   = 0
posWt-LFsSt LF.stVotes      = 0
posWt-LFsSt LF.stBlockRange = 0     -- offers api sendLFNext/LastBlock (τ-stuck)
posWt-LFsSt LF.stDone       = 0

posWt-LFs : LFsPos → ℕ
posWt-LFs (lfsHead st)    = posWt-LFsSt st
posWt-LFs (lfsSil  st)    = posWt-LFsSt st
posWt-LFs lfsDone1        = 0       -- offers doneLF (τ-stuck)
posWt-LFs (lfsWblk1 _)    = 2       -- send MsgLFBlock → lfsSil stIdle(1)
posWt-LFs (lfsWtxs1 _)    = 2
posWt-LFs (lfsWvot1 _)    = 2
posWt-LFs (lfsWnext1 _)   = 2       -- send MsgLFNextBlock → lfsSil stBlockRange(0)
posWt-LFs (lfsWlast1 _)   = 2       -- send MsgLFLastBlock → lfsSil stIdle(1)

-- TxSubmission CLIENT: auto-sends Init at `stInit`; at `stIdle` receives a
-- request (one recv → api-offer leaf); each reply-send drops back to `stIdle`.
posWt-TScSt : TS.TSState → ℕ
posWt-TScSt TS.stInit             = 2  -- send MsgTSInit → tcSil stIdle(1)
posWt-TScSt TS.stIdle             = 1  -- recv MsgTSRequestTxIds/Txs → tcReqIds*1/tcReqTxs1(0)
posWt-TScSt TS.stTxIdsBlocking    = 0  -- offers api sendTSReplyTxIds/sendTSDone (τ-stuck)
posWt-TScSt TS.stTxIdsNonBlocking = 0
posWt-TScSt TS.stTxs              = 0
posWt-TScSt TS.stDone             = 0

posWt-TSc : TScPos → ℕ
posWt-TSc (tcHead st)     = posWt-TScSt st
posWt-TSc (tcSil  st)     = posWt-TScSt st
posWt-TSc (tcReqIdsB1 _ _)  = 0    -- offers api recvTSRequestTxIds! (τ-stuck)
posWt-TSc (tcReqIdsNB1 _ _) = 0
posWt-TSc (tcReqTxs1 _)     = 0
posWt-TSc (tcRepB1 _)     = 2      -- send MsgTSReplyTxIds → tcSil stIdle(1)
posWt-TSc tcDone1         = 1      -- send MsgTSDone → tcSil stDone(0)
posWt-TSc (tcRepNB1 _)    = 2      -- send MsgTSReplyTxIds → tcSil stIdle(1)
posWt-TSc (tcRepTxs1 _)   = 2      -- send MsgTSReplyTxs → tcSil stIdle(1)

-- TxSubmission SERVER: auto-receives Init at `stInit`; at `stIdle` sends a
-- request (via api → one wire send → outstanding state); each reply-recv → stIdle.
posWt-TSsSt : TS.TSState → ℕ
posWt-TSsSt TS.stInit             = 1  -- recv MsgTSInit → tsSil stIdle(0)
posWt-TSsSt TS.stIdle             = 0  -- offers api sendTSRequest… (τ-stuck)
posWt-TSsSt TS.stTxIdsBlocking    = 1  -- recv MsgTSReplyTxIds → stIdle(0) / MsgTSDone → tsDone1(0)
posWt-TSsSt TS.stTxIdsNonBlocking = 1  -- recv MsgTSReplyTxIds → stIdle(0)
posWt-TSsSt TS.stTxs              = 1  -- recv MsgTSReplyTxs → stIdle(0)
posWt-TSsSt TS.stDone             = 0

posWt-TSs : TSsPos → ℕ
posWt-TSs (tsHead st)   = posWt-TSsSt st
posWt-TSs (tsSil  st)   = posWt-TSsSt st
posWt-TSs tsDone1       = 0        -- offers doneTS (τ-stuck)
posWt-TSs (tsReqB1 _)   = 2        -- send MsgTSRequestTxIds Blocking → tsSil stTxIdsBlocking(1)
posWt-TSs (tsReqNB1 _)  = 2        -- send MsgTSRequestTxIds NonBlocking → tsSil stTxIdsNonBlocking(1)
posWt-TSs (tsReqTxs1 _) = 2        -- send MsgTSRequestTxs → tsSil stTxs(1)

-- one link's inert-peer budget = the sum of its eight inert peer positions
posWt-Inert : InertPos → ℕ
posWt-Inert ip = posWt-TSc (tsc ip) + posWt-TSs (tss ip)
               + posWt-KAc (kac ip) + posWt-KAs (kas ip)
               + posWt-LNc (lnc ip) + posWt-LNs (lns ip)
               + posWt-LFc (lfc ip) + posWt-LFs (lfs ip)

------------------------------------------------------------------------
-- Per-node weights: sum of the CS/BF client+server budgets of each link the
-- node hosts + the per-link inert-peer (TS-Init) budget (the drivers
-- `prod`/`cp`/`cons` contribute 0).
------------------------------------------------------------------------

-- node A hosts the AB and AC producer legs (CS+BF client+server each)
nodeWtA : NodeStateA → ℕ
nodeWtA s = posWt-CSc (NodeStateA.csC-AB s) + posWt-CSs (NodeStateA.csS-AB s)
          + posWt-BFc (NodeStateA.bfC-AB s) + posWt-BFs (NodeStateA.bfS-AB s)
          + posWt-CSc (NodeStateA.csC-AC s) + posWt-CSs (NodeStateA.csS-AC s)
          + posWt-BFc (NodeStateA.bfC-AC s) + posWt-BFs (NodeStateA.bfS-AC s)
          + posWt-Inert (NodeStateA.inert-AB s) + posWt-Inert (NodeStateA.inert-AC s)

-- node B relays AB → BD
nodeWtB : NodeStateB → ℕ
nodeWtB s = posWt-CSc (NodeStateB.csC-AB s) + posWt-CSs (NodeStateB.csS-AB s)
          + posWt-BFc (NodeStateB.bfC-AB s) + posWt-BFs (NodeStateB.bfS-AB s)
          + posWt-CSc (NodeStateB.csC-BD s) + posWt-CSs (NodeStateB.csS-BD s)
          + posWt-BFc (NodeStateB.bfC-BD s) + posWt-BFs (NodeStateB.bfS-BD s)
          + posWt-Inert (NodeStateB.inert-AB s) + posWt-Inert (NodeStateB.inert-BD s)

-- node C relays AC → CD
nodeWtC : NodeStateC → ℕ
nodeWtC s = posWt-CSc (NodeStateC.csC-AC s) + posWt-CSs (NodeStateC.csS-AC s)
          + posWt-BFc (NodeStateC.bfC-AC s) + posWt-BFs (NodeStateC.bfS-AC s)
          + posWt-CSc (NodeStateC.csC-CD s) + posWt-CSs (NodeStateC.csS-CD s)
          + posWt-BFc (NodeStateC.bfC-CD s) + posWt-BFs (NodeStateC.bfS-CD s)
          + posWt-Inert (NodeStateC.inert-AC s) + posWt-Inert (NodeStateC.inert-CD s)

-- node D consumes BD and CD
nodeWtD : NodeStateD → ℕ
nodeWtD s = posWt-CSc (NodeStateD.csC-BD s) + posWt-CSs (NodeStateD.csS-BD s)
          + posWt-BFc (NodeStateD.bfC-BD s) + posWt-BFs (NodeStateD.bfS-BD s)
          + posWt-CSc (NodeStateD.csC-CD s) + posWt-CSs (NodeStateD.csS-CD s)
          + posWt-BFc (NodeStateD.bfC-CD s) + posWt-BFs (NodeStateD.bfS-CD s)
          + posWt-Inert (NodeStateD.inert-BD s) + posWt-Inert (NodeStateD.inert-CD s)

-- the whole abstract-node remaining-wire-event count
nodesWt : SysState → ℕ
nodesWt s = nodeWtA (nA s) + nodeWtB (nB s) + nodeWtC (nC s) + nodeWtD (nD s)

------------------------------------------------------------------------
-- THE MEASURE `μτ`.
------------------------------------------------------------------------

-- on a `SysState`: 3 · (node wire events) + (medium cell weight)
μτ-sys : SysState → ℕ
μτ-sys s = 3 * nodesWt s + medWt (med s)

-- on a reachable config (the WalkConv engine's `μτ : RState → ℕ`)
μτ : RState → ℕ
μτ r = μτ-sys (toSys r)

------------------------------------------------------------------------
-- THE TWO CLASS ARITHMETIC FACTS (the strict decrease each τ-class realises).
------------------------------------------------------------------------

-- 3·N′ + 3 = 3·suc N′ (fold the +3 back into the successor factor)
private
  3*N′+3 : ∀ N′ → 3 * N′ + 3 ≡ 3 * suc N′
  3*N′+3 N′ = trans (+-comm (3 * N′) 3) (sym (*-suc 3 N′))

-- io-SYNC class: if the node count strictly drops (`suc N′ ≤ N`) and the cell
-- summand rises by at most one (`C′ ≤ suc C`), then `μτ` strictly drops.  The
-- `3·` weight makes a −1 node drop dominate the +1 cell rise (3 > 1).
μτ-io-dec : ∀ {N′ N C′ C} → suc N′ ≤ N → C′ ≤ suc C → 3 * N′ + C′ < 3 * N + C
μτ-io-dec {N′} {N} {C′} {C} nlt clt = begin
    suc (3 * N′ + C′)          ≡⟨ sym (+-suc (3 * N′) C′) ⟩
    3 * N′ + suc C′            ≤⟨ +-mono-≤ (≤-refl {3 * N′}) (s≤s clt) ⟩
    3 * N′ + suc (suc C)       ≤⟨ +-mono-≤ (≤-refl {3 * N′}) (s≤s (s≤s (n≤1+n C))) ⟩
    3 * N′ + (3 + C)           ≡⟨ sym (+-assoc (3 * N′) 3 C) ⟩
    (3 * N′ + 3) + C           ≡⟨ cong (_+ C) (3*N′+3 N′) ⟩
    3 * suc N′ + C             ≤⟨ +-mono-≤ (*-monoʳ-≤ 3 nlt) (≤-refl {C}) ⟩
    3 * N + C                  ∎
  where open ≤-Reasoning

-- MEDIUM class: a medium-τ leaves the node count fixed and drains ONE cell
-- draining(2)→empty(0), so the cell summand drops by exactly 2 (`C′ + 2 ≡ C`);
-- `μτ` strictly drops.
μτ-med-dec : ∀ {N C′ C} → C′ + 2 ≡ C → 3 * N + C′ < 3 * N + C
μτ-med-dec {N} {C′} {C} eq = begin
    suc (3 * N + C′)       ≡⟨ sym (+-suc (3 * N) C′) ⟩
    3 * N + suc C′         ≤⟨ +-mono-≤ (≤-refl {3 * N}) (s≤s (n≤1+n C′)) ⟩
    3 * N + suc (suc C′)   ≡⟨ cong (3 * N +_) (+-comm 2 C′) ⟩
    3 * N + (C′ + 2)       ≡⟨ cong (3 * N +_) eq ⟩
    3 * N + C              ∎
  where open ≤-Reasoning

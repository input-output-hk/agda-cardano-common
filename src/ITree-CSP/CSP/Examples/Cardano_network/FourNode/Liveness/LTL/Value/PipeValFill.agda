{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the `PipeVal` io CLAUSE CORES (`Praos.PipeValFill`),
-- SESSION-37 step (ii) meat.
--
-- The genuinely NEW content of `PipeValStep.TauIoV`; the rest of that
-- combinator is a mechanical mirror of `PipeTauIo.tauIo-{in,out}` (same
-- `io-sync-wrun`, same ~20-constructor label split, same `pick*` selectors).
--
-- OPENING MOVE — the three-for-three lesson applied FIRST, not in hindsight.
-- Before proving anything, the producing sites were read for facts already
-- sitting there unclaimed.  It paid off a FOURTH time:
-- `PipeSrvFire.bundle-blkfill-srv′` returns `BFsHasBlk bfs` taken straight from
-- the DECISION `bfsHasBlk? bfs`, never from the step — so the payload↔position
-- value match (`the server at bsBlk1 b writes exactly MsgBlock b`) is
-- short-circuited away before it can be observed.  `blockFill-srv-pins` below
-- recovers it, and it needs only ONE clause: the other ten server positions are
-- already refuted by the frozen `PipeFillSource.blockFill-forces-srv`.
--
-- CONTENTS
--   (1) `blockFill-srv-pins` — a BF server at `bsBlk1 b` fires the cell-filling
--       io ONLY with the payload `MsgBlock b` (the value pin, at the LTS level;
--       `PipeValGate.srv-wblk-pins` is the table-level statement of the same
--       row).  This is the fill arm's whole content.
--   (2) `hasBlk⇒isBlk1` — `BFsHasBlk bfs` NAMES the held block, so the frozen
--       `PipeSrvFire.srvHit-{up,dn}` output can be turned into a position.
--   (3) the three one-liner arms of `TauIoV`, by construction-case:
--       `notHasBlk⇒SrvValOK`, `notHasBlk⇒CliValOK`,
--       `cellValOK-full⇒draining` (the OUTPUT arm's whole content — a drain
--       keeps the payload, and `CellValOK` reads only the message).
--   (4) `cliRead⇒CliValOK` — the drain-into-client arm: the leg's own cell held
--       `blkA` and the reader's `CliBlkVal` names the same block, so the reader
--       holds `blkA`.  This is what session 36's `CliBlkVal` strengthening of
--       `PipeCliIoDec`/`PipeBundleIoEvo`/`PipeNodeIoEvo` was FOR.
--
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( Dec; yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; _≢_; refl; sym; trans; cong; subst )

open import Class.DecEq using ( DecEq; _≟_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Block; time₀; length₀ )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; hi; N2N_BlockFetch; FromResponder )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; input; recvBFBlock; sendBFBlock; apiBF )
open import CSP.Examples.Cardano_network.Data p

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; sVis )

import CSP.Examples.Cardano_network.BlockFetch p as BF

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA using
  ( BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil
  ; BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
  ; decProd; ProdPh; pp5 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA using
  ( NetProc; absBFs; coarsenBFs; absBundleG; absBFc; coarsenBFc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA using
  ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink5 blkA using ( Tbfs; Tbfc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; empty; full; draining )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( PlIsBlk )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeCliIoDec blkA as CLI
open CLI using ( CliBlkVal )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( MsgValOK; CellValOK; SrvValOK; CliValOK )
-- the 12-peer bundle no-offer and the client's never-sends-a-block fact are
-- ALREADY exported and ALREADY parametric in the two BF peers' own no-offers —
-- so the bundle-level value lemma below needs no edit to `PipeSrvFire` at all
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvFire blkA
  using ( bundleG-io-no-BF; blockFill-forces-cli )
-- the bundle BF-peer eliminator is ALREADY parametric in BOTH peer facts (it
-- takes them as continuations returning an arbitrary `R`), so the value-carrying
-- bundle lemma below needs no edit to `PipeBundleRecv` either
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleRecv blkA
  using ( bundleBF-ev-forces; recvBFBlock-server-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeRecvSource blkA
  using ( recvBFBlock-forces-src )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( CScPos; CSsPos; InertPos )

------------------------------------------------------------------------
-- (1) THE FILL VALUE PIN.  The one fact `PipeSrvFire`'s decision threw away.
------------------------------------------------------------------------

-- the `MsgBlock b` wire payload of a responder-side BF sender
blkPayload : Block → Payload
blkPayload b = time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)

-- a BF SERVER at `bsBlk1 b` fires the cell-filling io ONLY with the payload
-- `MsgBlock b`: the abstract table row `bfSnxt … (bsWblk b) (input …) pl` is
-- gated on `pl ≟ blkPayload b`, so the fired payload IS the held block's
blockFill-srv-pins :
    (l : Link) (d : Dir) (b : Block)
    {l′ : Link} {d′ : Dir} {pl : Payload} {M : NetProc}
  → absBFs l d (bsBlk1 b) ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► M
  → pl ≡ blkPayload b
blockFill-srv-pins l d b {l′} {d′} {pl} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , _ with l′ ≟ l | d′ ≟ d
...   | no  _    | _     = ⊥-elim (nothing-absurd ceq)
...   | yes refl | no  _ = ⊥-elim (nothing-absurd ceq)
...   | yes refl | yes refl with pl ≟ blkPayload b
...     | no  _   = ⊥-elim (nothing-absurd ceq)
...     | yes peq = peq

------------------------------------------------------------------------
-- (2) `BFsHasBlk` NAMES the block.  `PipeSrvFire.srvHit-{up,dn}` hands back the
-- value-blind `BFsHasBlk`; `bsBlk1` is its only inhabited position, so the
-- position (and hence the block) is recoverable by a pure case split.
------------------------------------------------------------------------

-- a holding BF server is at `bsBlk1` — with the held block named
hasBlk⇒isBlk1 : (bfs : BFsPos) → BFsHasBlk bfs → Σ[ b ∈ Block ] bfs ≡ bsBlk1 b
hasBlk⇒isBlk1 (bsBlk1 b)   h = b , refl
hasBlk⇒isBlk1 (bsHead _)   ()
hasBlk⇒isBlk1 (bsReq1 _)   ()
hasBlk⇒isBlk1 bsDone1      ()
hasBlk⇒isBlk1 bsStart1     ()
hasBlk⇒isBlk1 bsNoBlk1     ()
hasBlk⇒isBlk1 bsBatchDone1 ()
hasBlk⇒isBlk1 (bsSil _)    ()

------------------------------------------------------------------------
-- (3) THE THREE ONE-LINER ARMS.
------------------------------------------------------------------------

-- a BF server that holds NO block satisfies the value clause vacuously
notHasBlk⇒SrvValOK : (bfs : BFsPos) → (BFsHasBlk bfs → ⊥) → SrvValOK bfs
notHasBlk⇒SrvValOK (bsBlk1 b)   ¬h = ⊥-elim (¬h tt)
notHasBlk⇒SrvValOK (bsHead _)   ¬h = tt
notHasBlk⇒SrvValOK (bsReq1 _)   ¬h = tt
notHasBlk⇒SrvValOK bsDone1      ¬h = tt
notHasBlk⇒SrvValOK bsStart1     ¬h = tt
notHasBlk⇒SrvValOK bsNoBlk1     ¬h = tt
notHasBlk⇒SrvValOK bsBatchDone1 ¬h = tt
notHasBlk⇒SrvValOK (bsSil _)    ¬h = tt

-- a BF client that holds NO block satisfies the value clause vacuously
notHasBlk⇒CliValOK : (bfc : BFcPos) → (BFcHasBlk bfc → ⊥) → CliValOK bfc
notHasBlk⇒CliValOK (bcBlk1 b) ¬h = ⊥-elim (¬h tt)
notHasBlk⇒CliValOK (bcHead _) ¬h = tt
notHasBlk⇒CliValOK (bcReq1 _) ¬h = tt
notHasBlk⇒CliValOK bcDone1    ¬h = tt
notHasBlk⇒CliValOK (bcSil _)  ¬h = tt

-- the OUTPUT arm's whole content: a drain keeps the payload, and `CellValOK`
-- reads only the message, so the value clause survives `full x → draining x`
cellValOK-full⇒draining : (x : Payload) → CellValOK (full x) → CellValOK (draining x)
cellValOK-full⇒draining (_ , _ , _ , m) h = h

-- and back, for the direction the client-read arm needs
cellValOK-draining⇒full : (x : Payload) → CellValOK (draining x) → CellValOK (full x)
cellValOK-draining⇒full (_ , _ , _ , m) h = h

------------------------------------------------------------------------
-- (4) THE DRAIN-INTO-CLIENT ARM.  This is what session 36's `CliBlkVal`
-- strengthening was for: the reader's successor position is pinned to the block
-- the payload carried, so the leg's own cell clause hands the reader its value.
------------------------------------------------------------------------

-- a reader whose `CliBlkVal` names the payload's block inherits the payload's
-- value clause: if the cell held `blkA`, the reader now holds `blkA`.
-- `PlIsBlk x` selects the ONE payload shape on which `CliBlkVal` is not vacuous
-- (`CliBlkVal` is `⊤` elsewhere, so the hypothesis is genuinely needed here).
cliRead⇒CliValOK : (bfc′ : BFcPos) (x : Payload)
                 → PlIsBlk x → CliBlkVal bfc′ x → CellValOK (full x) → CliValOK bfc′
cliRead⇒CliValOK bfc′ (_ , _ , _ , blockFetch (MsgBlock b))        pb cv h =
  subst CliValOK (sym cv) h
cliRead⇒CliValOK bfc′ (_ , _ , _ , blockFetch (MsgRequestRange _)) () cv h
cliRead⇒CliValOK bfc′ (_ , _ , _ , blockFetch MsgStartBatch)       () cv h
cliRead⇒CliValOK bfc′ (_ , _ , _ , blockFetch MsgNoBlocks)         () cv h
cliRead⇒CliValOK bfc′ (_ , _ , _ , blockFetch MsgBatchDone)        () cv h
cliRead⇒CliValOK bfc′ (_ , _ , _ , blockFetch MsgClientDone)       () cv h
cliRead⇒CliValOK bfc′ (_ , _ , _ , chainSync _)                    () cv h
cliRead⇒CliValOK bfc′ (_ , _ , _ , txSubmission _)                 () cv h
cliRead⇒CliValOK bfc′ (_ , _ , _ , keepAlive _)                    () cv h
cliRead⇒CliValOK bfc′ (_ , _ , _ , leiosNotify _)                  () cv h
cliRead⇒CliValOK bfc′ (_ , _ , _ , leiosFetch _)                   () cv h

------------------------------------------------------------------------
-- (5) THE BUNDLE-LEVEL VALUE FACT — refute the MISMATCH, do not extract the
-- step.
--
-- `PipeSrvFire` proves its bundle fact BY CONTRADICTION against a 12-peer
-- `⦀-noOffer` and therefore never extracts the server's own step, which
-- `blockFill-srv-pins` would need.  The fix is to use the SAME shape one notch
-- differently: `bundleG-io-no-BF` takes its two peer no-offers as ARGUMENTS, so
-- feeding it a server no-offer built from `blockFill-srv-pins` refutes a fill
-- whose payload is NOT the server's own block.  Three precedents in this module
-- family for the move: `bundle-blkfill-srv′`'s own `¬h` branch, `PipeBundleIoEvo`
-- parametrising `BFcDecodeP` over `Cf`, and session 36's free `BlkReadAt` index.
--
-- NO in-place edit of `PipeSrvFire` is needed — both helpers are already
-- exported and already parametric.
------------------------------------------------------------------------

-- `with`-free driver (the decision is an ARGUMENT, so no goal is
-- `with`-normalised — the `blkA`-parameterisation hazard `PipeSrvFire`'s own
-- `bundle-blkfill-srv′` note records)
bundle-blkfill-val′ : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (b : Block) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {pl : Payload} {Bd′ : NetProc}
  → (pl ≡ blkPayload b) ⊎ (pl ≡ blkPayload b → ⊥)
  → absBundleG l cl sv csc css bfc (bsBlk1 b) ip
      ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► Bd′
  → PlIsBlk pl
  → pl ≡ blkPayload b
bundle-blkfill-val′ l cl sv csc css bfc b ip (inj₁ eq) step blk = eq
bundle-blkfill-val′ l cl sv csc css bfc b ip {l′} {d′} (inj₂ ¬eq) step blk =
  ⊥-elim (bundleG-io-no-BF l cl sv csc css bfc (bsBlk1 b) ip {e₁ = BF.sendBF l′ d′}
            (λ o → blockFill-forces-cli l cl bfc (proj₂ o) blk)
            (λ o → ¬eq (blockFill-srv-pins l sv b (proj₂ o)))
            (_ , step))

-- a BLOCK-carrying cell fill out of a bundle whose SERVER sits at `bsBlk1 b`
-- carries EXACTLY that server's block
bundle-blkfill-val : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (b : Block) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {pl : Payload} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc (bsBlk1 b) ip
      ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► Bd′
  → PlIsBlk pl
  → pl ≡ blkPayload b
bundle-blkfill-val l cl sv csc css bfc b ip {l′} {d′} {pl} step blk =
  bundle-blkfill-val′ l cl sv csc css bfc b ip (dec (pl ≟ blkPayload b)) step blk
  where
  -- re-package the `Dec` as a ⊎ so the driver above stays `with`-free
  dec : Dec (pl ≡ blkPayload b) → (pl ≡ blkPayload b) ⊎ (pl ≡ blkPayload b → ⊥)
  dec (yes q) = inj₁ q
  dec (no ¬q) = inj₂ ¬q

-- the cell-value consequence: a fill by a server holding `blkA` writes a
-- payload whose value clause holds
blkfill-cellValOK : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (b : Block) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {pl : Payload} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc (bsBlk1 b) ip
      ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► Bd′
  → PlIsBlk pl
  → SrvValOK (bsBlk1 b)
  → CellValOK (full pl)
blkfill-cellValOK l cl sv csc css bfc b ip step blk sv-ok =
  subst (λ z → CellValOK (full z))
        (sym (bundle-blkfill-val l cl sv csc css bfc b ip step blk))
        sv-ok

------------------------------------------------------------------------
-- (6) THE CLIENT-SIDE api VALUE PIN — the twin of `blockFill-srv-pins`, and
-- the eighth instance of the dropped-value pattern.
--
-- `PipeRecvSource.recvBFBlock-forces-src` returns `BFcHasBlk bfc`, and its ONE
-- inhabited clause (`bcBlk1 b`) returns `tt` WITHOUT inspecting the step — yet
-- the abstract client table gates `recvBFBlock` at `bcAblk b` on `x ≟ b`
-- (`NodeSpecs.bfCnxt`, machine-checked as `PipeValGate.cli-ablk-pins`), so the
-- fired value IS the held block.  One clause, exactly like
-- `blockFill-srv-pins`: the other ten client positions are already refuted by
-- the frozen `recvBFBlock-forces-src`.
--
-- This is what `PipeEvDriverCone`'s `wUp`/`wDn` receive-coupling facts need in
-- order to hand `EvStepV` the recorded block's value.
------------------------------------------------------------------------

-- a BF CLIENT at `bcBlk1 b` fires the api `recvBFBlock` ONLY at the value `b`
recvBFBlock-src-val :
    (l : Link) (d : Dir) (b : Block)
    {l′ : Link} {d′ : Dir} {a : Block} {M : NetProc}
  → absBFc l d (bcBlk1 b)
      ─[ ev (evl (evLabel Block (ιBF (BF.apiBFev l′ d′ recvBFBlock)) a)) ]─► M
  → a ≡ b
recvBFBlock-src-val l d b {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , _ with l′ ≟ l | d′ ≟ d
...   | no  _    | _     = ⊥-elim (nothing-absurd ceq)
...   | yes refl | no  _ = ⊥-elim (nothing-absurd ceq)
...   | yes refl | yes refl with a ≟ b
...     | no  _   = ⊥-elim (nothing-absurd ceq)
...     | yes aeq = aeq

-- and its cash-out: a client whose value clause holds hands over `blkA`
recvBFBlock-src-blkA :
    (l : Link) (d : Dir) (b : Block)
    {l′ : Link} {d′ : Dir} {a : Block} {M : NetProc}
  → absBFc l d (bcBlk1 b)
      ─[ ev (evl (evLabel Block (ιBF (BF.apiBFev l′ d′ recvBFBlock)) a)) ]─► M
  → CliValOK (bcBlk1 b) → a ≡ blkA
recvBFBlock-src-blkA l d b step h = trans (recvBFBlock-src-val l d b step) h

------------------------------------------------------------------------
-- (7) THE CLIENT-POSITION PIN, peer and bundle level.  `wDn`/`wUp` in
-- `PipeEvDriverCone` currently report the value-blind `BFcHasBlk (dnClient l s)`;
-- what `EvStepV` needs is the POSITION at the fired value, so that the leg's
-- client clause (7) hands over the block the driver is about to record.
--
-- `PipeBundleRecv.bundleBF-ev-forces` takes BOTH peer facts as continuations
-- into an arbitrary `R`, so this reuses it verbatim — `PipeBundleRecv` is NOT
-- edited (the "check whether it is already parametric" rule, third time).
------------------------------------------------------------------------

-- a BF client that fires the api `recvBFBlock` at value `a` IS at `bcBlk1 a`
cliRecv-pos : (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {a : Block} {M : NetProc}
  → absBFc l d bfc
      ─[ ev (evl (evLabel Block (ιBF (BF.apiBFev l′ d′ recvBFBlock)) a)) ]─► M
  → bfc ≡ bcBlk1 a
cliRecv-pos l d (bcBlk1 b) step = cong bcBlk1 (sym (recvBFBlock-src-val l d b step))
cliRecv-pos l d (bcHead st) step = ⊥-elim (recvBFBlock-forces-src l d (bcHead st) step)
cliRecv-pos l d (bcReq1 r)  step = ⊥-elim (recvBFBlock-forces-src l d (bcReq1 r) step)
cliRecv-pos l d bcDone1     step = ⊥-elim (recvBFBlock-forces-src l d bcDone1 step)
cliRecv-pos l d (bcSil st)  step = ⊥-elim (recvBFBlock-forces-src l d (bcSil st) step)

-- the same at the BUNDLE level: a bundle that fires `recvBFBlock` at value `a`
-- has its CLIENT at `bcBlk1 a` (the server can never fire it —
-- `recvBFBlock-server-absurd`)
bundle-recv-cliPos :
    (l : Link) (cl sv : Dir) → cl ≢ sv
  → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {l′ : Link} {d′ : Dir} {a : Block} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip
       ─[ ev (evl (evLabel Block (ιBF (BF.apiBFev l′ d′ recvBFBlock)) a)) ]─► Bd′
  → bfc ≡ bcBlk1 a
bundle-recv-cliPos l cl sv cl≢sv csc css bfc bfs ip step =
  bundleBF-ev-forces l cl sv cl≢sv csc css bfc bfs ip
    (λ sC → cliRecv-pos l cl bfc sC)
    (λ sM → ⊥-elim (recvBFBlock-server-absurd l sv bfs sM))
    step

------------------------------------------------------------------------
-- (8) THE PRODUCER'S `!`-PIN, at the LTS level.  `PipeProdFire.decProd-sbb-pp5`
-- returns only the PHASE (`pp ≡ pp5`); the value the `!` pins is dropped, for
-- the tenth time in this campaign.  `PipeValGate.prod-pp5-output` +
-- `output-pins` already certify the pin at the TABLE level — this is the same
-- fact where the node dispatch can consume it.
--
-- One clause, same shape as `blockFill-srv-pins` and `recvBFBlock-src-val`:
-- the offer-map `with` is inlined (`output-ev-inv`'s idiom), because at `pp5`
-- the driver IS `Output (apiBF l d sendBFBlock) blk _`.
------------------------------------------------------------------------

-- node A's / a relay's produce driver at `pp5` fires `sendBFBlock` ONLY at the
-- block it was configured with
decProd-sbb-val : (l : Link) (d : Dir) (blk : Block) {b : Block} {M : NetProc}
  → decProd l d blk pp5
      ─[ ev (evl (evLabel Block (apiBF l d sendBFBlock) b)) ]─► M
  → b ≡ blk
decProd-sbb-val l d blk {b} (sVis refl br)
  with Net_Api-≟ {Payload} (Block , apiBF l d sendBFBlock) (Block , apiBF l d sendBFBlock)
... | no  ¬q   = ⊥-elim (¬q refl)
... | yes refl with b ≟ blk
...   | no  _  = ⊥-elim (nothing-absurd br)
...   | yes q  = q

-- and the cash-out node A needs: its driver is applied to the LITERAL `blkA`
-- (`SysNode.decNodeA`), so a `sendBFBlock` it fires carries `blkA`
decProd-sbb-blkA : (l : Link) (d : Dir) {b : Block} {M : NetProc}
  → decProd l d blkA pp5
      ─[ ev (evl (evLabel Block (apiBF l d sendBFBlock) b)) ]─► M
  → b ≡ blkA
decProd-sbb-blkA l d step = decProd-sbb-val l d blkA step

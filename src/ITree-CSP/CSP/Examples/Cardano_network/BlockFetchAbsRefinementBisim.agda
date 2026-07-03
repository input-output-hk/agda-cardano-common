{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Task 3: clientServerBF ∖ msgBF ≈DR BFabstractP ∖ msgBF, DIRECTLY as a
-- divergence-respecting weak bisimulation.
--
-- The implementation (client ∥ server, messages hidden) and the pipelined
-- spec REORDER two consecutive hidden τ's (the impl fires its loop-back τ
-- before the hidden message; the spec fires the hidden message before its
-- loop-back).  A strict Expansion preorder cannot match the reordered τ, but
-- a SYMMETRIC weak bisimulation (both directions τ*-padded) can — this module
-- builds it.  The transition oracle (Good `gA..gTb`, goodP-*, the per-state
-- `*-τ`/`*-noτ` step lemmas, impl-noDiv/specP-noDiv) is reused verbatim from
-- `BlockFetchAbsRefinement`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.BlockFetchAbsRefinementBisim (p : Params) where

open import Level using (lift)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; ≡-≟-identity)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

open import CSP.Examples.Cardano_network.BlockFetch p
open import CSP.Examples.Cardano_network.Net p
  using ( ApiBFTag; ApiBFCar
        ; sendBFRequestRange; sendBFClientDone; sendBFStartBatch
        ; sendBFNoBlocks; sendBFBlock; sendBFBatchDone; recvBFBlock; reqBFRange )
open import CSP.Examples.Cardano_network.Data p using (ChainRange; DecEq-ChainRange)
open Params p

open import Semantics.LTS {E = BFAbsEv} {I = ExtI BFAbsEv}
open import Semantics.WeakBisim {E = BFAbsEv} {I = ExtI BFAbsEv}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF; τ*-trans)
open import Semantics.DRBisim {E = BFAbsEv} {I = ExtI BFAbsEv}
  using (Diverges; DRbisim; _≈DR_; drbisim-sym)
open import Semantics.FailuresDivergences {E = BFAbsEv} {I = ExtI BFAbsEv}
  using (_⊑FD_; _≈FD_)
open import Semantics.DRImpliesFD {E = BFAbsEv} {I = ExtI BFAbsEv}
  using (drbisim→≈FD)

open import CSP.Laws.Traces.TraceLawsHide BFAbsEv-≟
  using (Hide-τ; Hide-keep; Hide-hidden; Hide-√
        ; Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√)
open import CSP.Laws.Traces.TraceLawsParallel BFAbsEv-≟
  using (Par-τ-L; Par-τ-R; Par-sync; Par-soloL; Par-soloR)
open import CSP.Laws.Traces.TraceLawsParallelElim BFAbsEv-≟
  using (Par-τ-elim; ParτR; τL; τR
        ; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)

-- the committed transition oracle (Good gA..gTb, goodP-*, step lemmas, noDiv).
open import CSP.Examples.Cardano_network.BlockFetchAbsRefinement p

open AbsOps using (_∖_; Par⊤; Par; iter; Ret; Output; Prefix; Prefix₀; pchoice; viewV; EventSet)
open Good
open DRbisim
open WSimF

------------------------------------------------------------------------
-- The (multi-valued) bisimulation relation between impl states (`JP …`) and
-- spec states (`ITP …`/`P-…`), one constructor per GFP-related pair.  The
-- carriers are spelled out explicitly so that `mkDR` can invert/construct the
-- exact composite steps via the committed step lemmas + the intro lemmas.
data RState : PTree BFAbsEv (ExtI BFAbsEv) Rr
            → PTree BFAbsEv (ExtI BFAbsEv) Rr → Set where
  -- idle / request / client-done region
  rsA  : RState (JP (IC stIdle) (IS stIdle))           (ITP pIdle ∖ msgBF)
  rsB  : ∀ r → RState (JP (CB-req r) (IS stIdle))       (P-req r ∖ msgBF)
  rsTa : ∀ r → RState (JP (CB-req r) (SB-loop stIdle))   (P-req r ∖ msgBF)
  rsD  : ∀ r → RState (JP (CB-loop stBusy) (SB-req r))   (P-req2 r ∖ msgBF)
  rsF  : ∀ r → RState (JP (IC stBusy) (SB-req r))        (P-req2 r ∖ msgBF)
  rsC  : RState (JP CB-cdone (IS stIdle))                (P-cdone ∖ msgBF)
  rsTb : RState (JP CB-cdone (SB-loop stIdle))           (P-cdone ∖ msgBF)
  rsE  : RState (JP (CB-loop stDone) (SB-loop stDone))   (P-loop pDone ∖ msgBF)
  rsE1 : RState (JP (IC stDone) (SB-loop stDone))        (P-loop pDone ∖ msgBF)
  rsE2 : RState (JP (CB-loop stDone) (IS stDone))        (P-loop pDone ∖ msgBF)
  rsZ  : RState (JP (IC stDone) (IS stDone))             (ITP pDone ∖ msgBF)
  -- busy region
  rsG  : RState (JP (CB-loop stBusy) (SB-loop stBusy))   (ITP pBusy ∖ msgBF)
  rsH  : RState (JP (IC stBusy) (SB-loop stBusy))        (ITP pBusy ∖ msgBF)
  rsI  : RState (JP (CB-loop stBusy) (IS stBusy))        (ITP pBusy ∖ msgBF)
  rsJ  : RState (JP (IC stBusy) (IS stBusy))             (ITP pBusy ∖ msgBF)
  -- start-batch / no-blocks region
  rsK  : RState (JP (CB-loop stBusy) SB-sbatch)          (P-sbatch ∖ msgBF)
  rsM  : RState (JP (IC stBusy) SB-sbatch)               (P-sbatch ∖ msgBF)
  rsL  : RState (JP (CB-loop stBusy) SB-noblk)           (P-noblk ∖ msgBF)
  rsN  : RState (JP (IC stBusy) SB-noblk)                (P-noblk ∖ msgBF)
  -- streaming-entry region
  rsP  : RState (JP (CB-loop stStreaming) (SB-loop stStreaming)) (P-loop pStr0 ∖ msgBF)
  rsR  : RState (JP (IC stStreaming) (SB-loop stStreaming))      (ITP pStr0 ∖ msgBF)
  rsS  : RState (JP (CB-loop stStreaming) (IS stStreaming))      (ITP pStr0 ∖ msgBF)
  rsV  : RState (JP (IC stStreaming) (IS stStreaming))           (ITP pStr0 ∖ msgBF)
  -- idle-loopback region
  rsQ  : RState (JP (CB-loop stIdle) (SB-loop stIdle))   (P-loop pIdle ∖ msgBF)
  rsT  : RState (JP (IC stIdle) (SB-loop stIdle))        (ITP pIdle ∖ msgBF)
  rsU  : RState (JP (CB-loop stIdle) (IS stIdle))        (P-loop pIdle ∖ msgBF)
  -- streaming-block region
  rsW  : ∀ b → RState (JP (IC stStreaming) (SB-blk b))           (P-blk0 b ∖ msgBF)
  rsW2 : ∀ b → RState (JP (CB-blk b) (SB-loop stStreaming))      (P-loop (pStr1 b) ∖ msgBF)
  rsW3 : ∀ b → RState (JP (CB-blk b) (IS stStreaming))           (ITP (pStr1 b) ∖ msgBF)
  rsW4 : ∀ b b′ → RState (JP (CB-blk b) (SB-blk b′))             (ITP (pStr2 b b′) ∖ msgBF)
  rsW5 : ∀ b → RState (JP (CB-blk b) SB-bdone)                   (ITP (pStrD b) ∖ msgBF)
  rsW6 : ∀ b → RState (JP (CB-loop stStreaming) (SB-blk b))      (P-blk0 b ∖ msgBF)
  rsW7 : RState (JP (CB-loop stStreaming) SB-bdone)              (P-bdone ∖ msgBF)
  rsY  : RState (JP (IC stStreaming) SB-bdone)                   (P-bdone ∖ msgBF)
  -- extra MULTI-VALUED streaming pairs the GFP needs (report: gS↔P-loop pStr0
  -- alongside gS↔ITP pStr0; gW6↔P-blkD alongside gW6↔P-blk0).
  rsS′  : RState (JP (CB-loop stStreaming) (IS stStreaming))     (P-loop pStr0 ∖ msgBF)
  rsW6′ : ∀ b → RState (JP (CB-loop stStreaming) (SB-blk b))     (P-blkD b ∖ msgBF)
  -- (gG ↔ P-loop pBusy): the reqBFRange ev-successor of P-req2 (before its loop-back τ).
  rsGp : RState (JP (CB-loop stBusy) (SB-loop stBusy))           (P-loop pBusy ∖ msgBF)
  rsHp : RState (JP (IC stBusy) (SB-loop stBusy))                (P-loop pBusy ∖ msgBF)
  rsWp : ∀ b → RState (JP (IC stStreaming) (SB-blk b))           (P-loop (pStr1 b) ∖ msgBF)
  rsW4p : ∀ b b′ → RState (JP (CB-blk b) (SB-blk b′))            (P-blkP b b′ ∖ msgBF)
  rsW4q : ∀ b b′ → RState (JP (CB-blk b) (SB-blk b′))            (P-loop (pStr2 b b′) ∖ msgBF)
  rsW5q : ∀ b → RState (JP (CB-blk b) SB-bdone)                  (P-loop (pStrD b) ∖ msgBF)
  -- terminal: deadlock ≈DR deadlock (the √-successor on both sides).
  rsDL : RState deadlock deadlock


------------------------------------------------------------------------
-- diagonal decidability helpers (unblock value-restricted Output offers).
------------------------------------------------------------------------
-- ChainRange diagonal: `r ≟ r ≡ yes refl`.
≟-diagR : ∀ (r : ChainRange) → (r ≟ r) ≡ yes refl
≟-diagR r = ≡-≟-identity _≟_ refl

-- Block diagonal: `b ≟ b ≡ yes refl`.
≟-diagB : ∀ (b : Block) → (b ≟ b) ≡ yes refl
≟-diagB b = ≡-≟-identity _≟_ refl

------------------------------------------------------------------------
-- event-label abbreviations for the API events (all ∉ msgBF).
------------------------------------------------------------------------
evReq : ChainRange → Event√ Rr
evReq r = evl (evLabel (ApiBFCar sendBFRequestRange) (apiBF sendBFRequestRange) r)
evCDone : Event√ Rr
evCDone = evl (evLabel (ApiBFCar sendBFClientDone) (apiBF sendBFClientDone) tt)
evSBatch : Event√ Rr
evSBatch = evl (evLabel (ApiBFCar sendBFStartBatch) (apiBF sendBFStartBatch) tt)
evNoBlk : Event√ Rr
evNoBlk = evl (evLabel (ApiBFCar sendBFNoBlocks) (apiBF sendBFNoBlocks) tt)
evSBlk : Block → Event√ Rr
evSBlk b = evl (evLabel (ApiBFCar sendBFBlock) (apiBF sendBFBlock) b)
evBDone : Event√ Rr
evBDone = evl (evLabel (ApiBFCar sendBFBatchDone) (apiBF sendBFBatchDone) tt)
evRecv : Block → Event√ Rr
evRecv b = evl (evLabel (ApiBFCar recvBFBlock) (apiBF recvBFBlock) b)
evReqR : ChainRange → Event√ Rr
evReqR r = evl (evLabel (ApiBFCar reqBFRange) (apiBF reqBFRange) r)

------------------------------------------------------------------------
-- SPEC api steps (Hide-keep of the iter offer; api ∉ msgBF).
------------------------------------------------------------------------
sp-pIdle-req : ∀ r → (ITP pIdle ∖ msgBF) ─[ ev (evReq r) ]─► (P-req r ∖ msgBF)
sp-pIdle-req r = Hide-keep msgBF (ITP pIdle) (λ z → z) (sVis refl refl)

sp-pIdle-cdone : (ITP pIdle ∖ msgBF) ─[ ev evCDone ]─► (P-cdone ∖ msgBF)
sp-pIdle-cdone = Hide-keep msgBF (ITP pIdle) (λ z → z) (sVis refl refl)

sp-pBusy-sbatch : (ITP pBusy ∖ msgBF) ─[ ev evSBatch ]─► (P-sbatch ∖ msgBF)
sp-pBusy-sbatch = Hide-keep msgBF (ITP pBusy) (λ z → z) (sVis refl refl)

sp-pBusy-noblk : (ITP pBusy ∖ msgBF) ─[ ev evNoBlk ]─► (P-noblk ∖ msgBF)
sp-pBusy-noblk = Hide-keep msgBF (ITP pBusy) (λ z → z) (sVis refl refl)

sp-pStr0-blk : ∀ b → (ITP pStr0 ∖ msgBF) ─[ ev (evSBlk b) ]─► (P-blk0 b ∖ msgBF)
sp-pStr0-blk b = Hide-keep msgBF (ITP pStr0) (λ z → z) (sVis refl refl)

sp-pStr0-bdone : (ITP pStr0 ∖ msgBF) ─[ ev evBDone ]─► (P-bdone ∖ msgBF)
sp-pStr0-bdone = Hide-keep msgBF (ITP pStr0) (λ z → z) (sVis refl refl)

sp-pStr1-recv : ∀ b → (ITP (pStr1 b) ∖ msgBF) ─[ ev (evRecv b) ]─► (P-loop pStr0 ∖ msgBF)
sp-pStr1-recv b = Hide-keep msgBF (ITP (pStr1 b)) (λ z → z) (sVis refl (h b))
  where
  h : ∀ b → viewV (PTree.force (ITP (pStr1 b))) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (P-loop pStr0)
  h b rewrite ≟-diagB b = refl

sp-pStr1-blk : ∀ b b′ → (ITP (pStr1 b) ∖ msgBF) ─[ ev (evSBlk b′) ]─► (P-blkP b b′ ∖ msgBF)
sp-pStr1-blk b b′ = Hide-keep msgBF (ITP (pStr1 b)) (λ z → z) (sVis refl refl)

sp-pStr1-bdone : ∀ b → (ITP (pStr1 b) ∖ msgBF) ─[ ev evBDone ]─► (P-loop (pStrD b) ∖ msgBF)
sp-pStr1-bdone b = Hide-keep msgBF (ITP (pStr1 b)) (λ z → z) (sVis refl refl)

sp-pStr2-recv : ∀ b b′ → (ITP (pStr2 b b′) ∖ msgBF) ─[ ev (evRecv b) ]─► (P-blkD b′ ∖ msgBF)
sp-pStr2-recv b b′ = Hide-keep msgBF (ITP (pStr2 b b′)) (λ z → z) (sVis refl (h b b′))
  where
  h : ∀ b b′ → viewV (PTree.force (ITP (pStr2 b b′))) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (P-blkD b′)
  h b b′ rewrite ≟-diagB b = refl

sp-pStrD-recv : ∀ b → (ITP (pStrD b) ∖ msgBF) ─[ ev (evRecv b) ]─► (P-bdone ∖ msgBF)
sp-pStrD-recv b = Hide-keep msgBF (ITP (pStrD b)) (λ z → z) (sVis refl (h b))
  where
  h : ∀ b → viewV (PTree.force (ITP (pStrD b))) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (P-bdone)
  h b rewrite ≟-diagB b = refl

sp-preq2-reqR : ∀ r → (P-req2 r ∖ msgBF) ─[ ev (evReqR r) ]─► (P-loop pBusy ∖ msgBF)
sp-preq2-reqR r = Hide-keep msgBF (P-req2 r) (λ z → z) (sVis refl (h r))
  where
  h : ∀ r → viewV (PTree.force (P-req2 r)) (ApiBFCar reqBFRange , apiBF reqBFRange) r ≡ just (P-loop pBusy)
  h r rewrite ≟-diagR r = refl

------------------------------------------------------------------------
-- SPEC hidden-message τ steps (Hide-hidden of the Msg offer) and loop-back τ.
------------------------------------------------------------------------
sp-Preq-τ : ∀ r → (P-req r ∖ msgBF) ─[ τ ]─► (P-req2 r ∖ msgBF)
sp-Preq-τ r = Hide-hidden msgBF (P-req r) Poly.tt (sVis refl (h r))
  where
  h : ∀ r → viewV (PTree.force (P-req r)) (ChainRange , MsgRequestRange) r ≡ just (P-req2 r)
  h r rewrite ≟-diagR r = refl

sp-Pblk0-τ : ∀ b → (P-blk0 b ∖ msgBF) ─[ τ ]─► (P-loop (pStr1 b) ∖ msgBF)
sp-Pblk0-τ b = Hide-hidden msgBF (P-blk0 b) Poly.tt (sVis refl (h b))
  where
  h : ∀ b → viewV (PTree.force (P-blk0 b)) (Block , MsgBlock) b ≡ just (P-loop (pStr1 b))
  h b rewrite ≟-diagB b = refl

sp-PblkP-τ : ∀ b b′ → (P-blkP b b′ ∖ msgBF) ─[ τ ]─► (P-loop (pStr2 b b′) ∖ msgBF)
sp-PblkP-τ b b′ = Hide-hidden msgBF (P-blkP b b′) Poly.tt (sVis refl (h b b′))
  where
  h : ∀ b b′ → viewV (PTree.force (P-blkP b b′)) (Block , MsgBlock) b′ ≡ just (P-loop (pStr2 b b′))
  h b b′ rewrite ≟-diagB b′ = refl

sp-PblkD-τ : ∀ b′ → (P-blkD b′ ∖ msgBF) ─[ τ ]─► (P-loop (pStr1 b′) ∖ msgBF)
sp-PblkD-τ b′ = Hide-hidden msgBF (P-blkD b′) Poly.tt (sVis refl (h b′))
  where
  h : ∀ b′ → viewV (PTree.force (P-blkD b′)) (Block , MsgBlock) b′ ≡ just (P-loop (pStr1 b′))
  h b′ rewrite ≟-diagB b′ = refl

sp-Pcdone-τ : (P-cdone ∖ msgBF) ─[ τ ]─► (P-loop pDone ∖ msgBF)
sp-Pcdone-τ = Hide-hidden msgBF P-cdone Poly.tt (sVis refl refl)

sp-Psbatch-τ : (P-sbatch ∖ msgBF) ─[ τ ]─► (P-loop pStr0 ∖ msgBF)
sp-Psbatch-τ = Hide-hidden msgBF P-sbatch Poly.tt (sVis refl refl)

sp-Pnoblk-τ : (P-noblk ∖ msgBF) ─[ τ ]─► (P-loop pIdle ∖ msgBF)
sp-Pnoblk-τ = Hide-hidden msgBF P-noblk Poly.tt (sVis refl refl)

sp-Pbdone-τ : (P-bdone ∖ msgBF) ─[ τ ]─► (P-loop pIdle ∖ msgBF)
sp-Pbdone-τ = Hide-hidden msgBF P-bdone Poly.tt (sVis refl refl)

sp-Ploop-τ : ∀ s → (P-loop s ∖ msgBF) ─[ τ ]─► (ITP s ∖ msgBF)
sp-Ploop-τ s = Hide-τ msgBF (P-loop s) (sSil refl)

------------------------------------------------------------------------
-- IMPL leaf api emits (single peer).
------------------------------------------------------------------------
-- client at idle.
cl-IC-req : ∀ r → (IC stIdle) ─[ ev (evReq r) ]─► (CB-req r)
cl-IC-req r = sVis refl refl
cl-IC-cdone : (IC stIdle) ─[ ev evCDone ]─► CB-cdone
cl-IC-cdone = sVis refl refl
-- client delivering a queued block (value-restricted to b).
cl-CBblk-recv : ∀ b → (CB-blk b) ─[ ev (evRecv b) ]─► (CB-loop stStreaming)
cl-CBblk-recv b = sVis refl (h b)
  where
  h : ∀ b → viewV (PTree.force (CB-blk b)) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ just (CB-loop stStreaming)
  h b rewrite ≟-diagB b = refl
-- server notifying a request (value-restricted to r).
sv-SBreq-reqR : ∀ r → (SB-req r) ─[ ev (evReqR r) ]─► (SB-loop stBusy)
sv-SBreq-reqR r = sVis refl (h r)
  where
  h : ∀ r → viewV (PTree.force (SB-req r)) (ApiBFCar reqBFRange , apiBF reqBFRange) r ≡ just (SB-loop stBusy)
  h r rewrite ≟-diagR r = refl
-- server at busy.
sv-IS-sbatch : (IS stBusy) ─[ ev evSBatch ]─► SB-sbatch
sv-IS-sbatch = sVis refl refl
sv-IS-noblk : (IS stBusy) ─[ ev evNoBlk ]─► SB-noblk
sv-IS-noblk = sVis refl refl
-- server at streaming.
sv-IS-blk : ∀ b → (IS stStreaming) ─[ ev (evSBlk b) ]─► (SB-blk b)
sv-IS-blk b = sVis refl refl
sv-IS-bdone : (IS stStreaming) ─[ ev evBDone ]─► SB-bdone
sv-IS-bdone = sVis refl refl

------------------------------------------------------------------------
-- partner NON-OFFER proofs (the idle operand does not offer the solo api).
------------------------------------------------------------------------
no-IS-req : ∀ r → viewV (PTree.force (IS stIdle)) (ApiBFCar sendBFRequestRange , apiBF sendBFRequestRange) r ≡ nothing
no-IS-req r = refl
no-IS-cdone : viewV (PTree.force (IS stIdle)) (ApiBFCar sendBFClientDone , apiBF sendBFClientDone) tt ≡ nothing
no-IS-cdone = refl
no-SBloopIdle-req : ∀ r → viewV (PTree.force (SB-loop stIdle)) (ApiBFCar sendBFRequestRange , apiBF sendBFRequestRange) r ≡ nothing
no-SBloopIdle-req r = refl
no-SBloopIdle-cdone : viewV (PTree.force (SB-loop stIdle)) (ApiBFCar sendBFClientDone , apiBF sendBFClientDone) tt ≡ nothing
no-SBloopIdle-cdone = refl
no-CBloopBusy-reqR : ∀ r → viewV (PTree.force (CB-loop stBusy)) (ApiBFCar reqBFRange , apiBF reqBFRange) r ≡ nothing
no-CBloopBusy-reqR r = refl
no-ICbusy-reqR : ∀ r → viewV (PTree.force (IC stBusy)) (ApiBFCar reqBFRange , apiBF reqBFRange) r ≡ nothing
no-ICbusy-reqR r = refl
no-CBloopBusy-sbatch : viewV (PTree.force (CB-loop stBusy)) (ApiBFCar sendBFStartBatch , apiBF sendBFStartBatch) tt ≡ nothing
no-CBloopBusy-sbatch = refl
no-CBloopBusy-noblk : viewV (PTree.force (CB-loop stBusy)) (ApiBFCar sendBFNoBlocks , apiBF sendBFNoBlocks) tt ≡ nothing
no-CBloopBusy-noblk = refl
no-ICbusy-sbatch : viewV (PTree.force (IC stBusy)) (ApiBFCar sendBFStartBatch , apiBF sendBFStartBatch) tt ≡ nothing
no-ICbusy-sbatch = refl
no-ICbusy-noblk : viewV (PTree.force (IC stBusy)) (ApiBFCar sendBFNoBlocks , apiBF sendBFNoBlocks) tt ≡ nothing
no-ICbusy-noblk = refl
no-CBloopStr-blk : ∀ b → viewV (PTree.force (CB-loop stStreaming)) (ApiBFCar sendBFBlock , apiBF sendBFBlock) b ≡ nothing
no-CBloopStr-blk b = refl
no-CBloopStr-bdone : viewV (PTree.force (CB-loop stStreaming)) (ApiBFCar sendBFBatchDone , apiBF sendBFBatchDone) tt ≡ nothing
no-CBloopStr-bdone = refl
no-ICstr-blk : ∀ b → viewV (PTree.force (IC stStreaming)) (ApiBFCar sendBFBlock , apiBF sendBFBlock) b ≡ nothing
no-ICstr-blk b = refl
no-ICstr-bdone : viewV (PTree.force (IC stStreaming)) (ApiBFCar sendBFBatchDone , apiBF sendBFBatchDone) tt ≡ nothing
no-ICstr-bdone = refl
no-SBloopStr-recv : ∀ b → viewV (PTree.force (SB-loop stStreaming)) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ nothing
no-SBloopStr-recv b = refl
no-ISstr-recv : ∀ b → viewV (PTree.force (IS stStreaming)) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ nothing
no-ISstr-recv b = refl
no-SBblk-recv : ∀ b′ b → viewV (PTree.force (SB-blk b′)) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ nothing
no-SBblk-recv b′ b = refl
no-SBbdone-recv : ∀ b → viewV (PTree.force SB-bdone) (ApiBFCar recvBFBlock , apiBF recvBFBlock) b ≡ nothing
no-SBbdone-recv b = refl

------------------------------------------------------------------------
-- IMPL composite api solo steps (Hide-keep of a Par-solo; api ∉ msgBF).
------------------------------------------------------------------------
im-A-req : ∀ r → JP (IC stIdle) (IS stIdle) ─[ ev (evReq r) ]─► JP (CB-req r) (IS stIdle)
im-A-req r = Hide-keep msgBF (Par msgBF mrg (IC stIdle) (IS stIdle)) (λ z → z)
  (Par-soloL msgBF mrg (IC stIdle) (IS stIdle) (λ z → z) (cl-IC-req r) (no-IS-req r))
im-A-cdone : JP (IC stIdle) (IS stIdle) ─[ ev evCDone ]─► JP CB-cdone (IS stIdle)
im-A-cdone = Hide-keep msgBF (Par msgBF mrg (IC stIdle) (IS stIdle)) (λ z → z)
  (Par-soloL msgBF mrg (IC stIdle) (IS stIdle) (λ z → z) cl-IC-cdone no-IS-cdone)
im-T-req : ∀ r → JP (IC stIdle) (SB-loop stIdle) ─[ ev (evReq r) ]─► JP (CB-req r) (SB-loop stIdle)
im-T-req r = Hide-keep msgBF (Par msgBF mrg (IC stIdle) (SB-loop stIdle)) (λ z → z)
  (Par-soloL msgBF mrg (IC stIdle) (SB-loop stIdle) (λ z → z) (cl-IC-req r) (no-SBloopIdle-req r))
im-T-cdone : JP (IC stIdle) (SB-loop stIdle) ─[ ev evCDone ]─► JP CB-cdone (SB-loop stIdle)
im-T-cdone = Hide-keep msgBF (Par msgBF mrg (IC stIdle) (SB-loop stIdle)) (λ z → z)
  (Par-soloL msgBF mrg (IC stIdle) (SB-loop stIdle) (λ z → z) cl-IC-cdone no-SBloopIdle-cdone)
im-D-reqR : ∀ r → JP (CB-loop stBusy) (SB-req r) ─[ ev (evReqR r) ]─► JP (CB-loop stBusy) (SB-loop stBusy)
im-D-reqR r = Hide-keep msgBF (Par msgBF mrg (CB-loop stBusy) (SB-req r)) (λ z → z)
  (Par-soloR msgBF mrg (CB-loop stBusy) (SB-req r) (λ z → z) (sv-SBreq-reqR r) (no-CBloopBusy-reqR r))
im-F-reqR : ∀ r → JP (IC stBusy) (SB-req r) ─[ ev (evReqR r) ]─► JP (IC stBusy) (SB-loop stBusy)
im-F-reqR r = Hide-keep msgBF (Par msgBF mrg (IC stBusy) (SB-req r)) (λ z → z)
  (Par-soloR msgBF mrg (IC stBusy) (SB-req r) (λ z → z) (sv-SBreq-reqR r) (no-ICbusy-reqR r))
im-I-sbatch : JP (CB-loop stBusy) (IS stBusy) ─[ ev evSBatch ]─► JP (CB-loop stBusy) SB-sbatch
im-I-sbatch = Hide-keep msgBF (Par msgBF mrg (CB-loop stBusy) (IS stBusy)) (λ z → z)
  (Par-soloR msgBF mrg (CB-loop stBusy) (IS stBusy) (λ z → z) sv-IS-sbatch no-CBloopBusy-sbatch)
im-I-noblk : JP (CB-loop stBusy) (IS stBusy) ─[ ev evNoBlk ]─► JP (CB-loop stBusy) SB-noblk
im-I-noblk = Hide-keep msgBF (Par msgBF mrg (CB-loop stBusy) (IS stBusy)) (λ z → z)
  (Par-soloR msgBF mrg (CB-loop stBusy) (IS stBusy) (λ z → z) sv-IS-noblk no-CBloopBusy-noblk)
im-J-sbatch : JP (IC stBusy) (IS stBusy) ─[ ev evSBatch ]─► JP (IC stBusy) SB-sbatch
im-J-sbatch = Hide-keep msgBF (Par msgBF mrg (IC stBusy) (IS stBusy)) (λ z → z)
  (Par-soloR msgBF mrg (IC stBusy) (IS stBusy) (λ z → z) sv-IS-sbatch no-ICbusy-sbatch)
im-J-noblk : JP (IC stBusy) (IS stBusy) ─[ ev evNoBlk ]─► JP (IC stBusy) SB-noblk
im-J-noblk = Hide-keep msgBF (Par msgBF mrg (IC stBusy) (IS stBusy)) (λ z → z)
  (Par-soloR msgBF mrg (IC stBusy) (IS stBusy) (λ z → z) sv-IS-noblk no-ICbusy-noblk)
im-S-blk : ∀ b → JP (CB-loop stStreaming) (IS stStreaming) ─[ ev (evSBlk b) ]─► JP (CB-loop stStreaming) (SB-blk b)
im-S-blk b = Hide-keep msgBF (Par msgBF mrg (CB-loop stStreaming) (IS stStreaming)) (λ z → z)
  (Par-soloR msgBF mrg (CB-loop stStreaming) (IS stStreaming) (λ z → z) (sv-IS-blk b) (no-CBloopStr-blk b))
im-S-bdone : JP (CB-loop stStreaming) (IS stStreaming) ─[ ev evBDone ]─► JP (CB-loop stStreaming) SB-bdone
im-S-bdone = Hide-keep msgBF (Par msgBF mrg (CB-loop stStreaming) (IS stStreaming)) (λ z → z)
  (Par-soloR msgBF mrg (CB-loop stStreaming) (IS stStreaming) (λ z → z) sv-IS-bdone no-CBloopStr-bdone)
im-V-blk : ∀ b → JP (IC stStreaming) (IS stStreaming) ─[ ev (evSBlk b) ]─► JP (IC stStreaming) (SB-blk b)
im-V-blk b = Hide-keep msgBF (Par msgBF mrg (IC stStreaming) (IS stStreaming)) (λ z → z)
  (Par-soloR msgBF mrg (IC stStreaming) (IS stStreaming) (λ z → z) (sv-IS-blk b) (no-ICstr-blk b))
im-V-bdone : JP (IC stStreaming) (IS stStreaming) ─[ ev evBDone ]─► JP (IC stStreaming) SB-bdone
im-V-bdone = Hide-keep msgBF (Par msgBF mrg (IC stStreaming) (IS stStreaming)) (λ z → z)
  (Par-soloR msgBF mrg (IC stStreaming) (IS stStreaming) (λ z → z) sv-IS-bdone no-ICstr-bdone)
im-W2-recv : ∀ b → JP (CB-blk b) (SB-loop stStreaming) ─[ ev (evRecv b) ]─► JP (CB-loop stStreaming) (SB-loop stStreaming)
im-W2-recv b = Hide-keep msgBF (Par msgBF mrg (CB-blk b) (SB-loop stStreaming)) (λ z → z)
  (Par-soloL msgBF mrg (CB-blk b) (SB-loop stStreaming) (λ z → z) (cl-CBblk-recv b) (no-SBloopStr-recv b))
im-W3-recv : ∀ b → JP (CB-blk b) (IS stStreaming) ─[ ev (evRecv b) ]─► JP (CB-loop stStreaming) (IS stStreaming)
im-W3-recv b = Hide-keep msgBF (Par msgBF mrg (CB-blk b) (IS stStreaming)) (λ z → z)
  (Par-soloL msgBF mrg (CB-blk b) (IS stStreaming) (λ z → z) (cl-CBblk-recv b) (no-ISstr-recv b))
im-W3-blk : ∀ b b′ → JP (CB-blk b) (IS stStreaming) ─[ ev (evSBlk b′) ]─► JP (CB-blk b) (SB-blk b′)
im-W3-blk b b′ = Hide-keep msgBF (Par msgBF mrg (CB-blk b) (IS stStreaming)) (λ z → z)
  (Par-soloR msgBF mrg (CB-blk b) (IS stStreaming) (λ z → z) (sv-IS-blk b′) (h b b′))
  where
  h : ∀ b b′ → viewV (PTree.force (CB-blk b)) (ApiBFCar sendBFBlock , apiBF sendBFBlock) b′ ≡ nothing
  h b b′ = refl
im-W3-bdone : ∀ b → JP (CB-blk b) (IS stStreaming) ─[ ev evBDone ]─► JP (CB-blk b) SB-bdone
im-W3-bdone b = Hide-keep msgBF (Par msgBF mrg (CB-blk b) (IS stStreaming)) (λ z → z)
  (Par-soloR msgBF mrg (CB-blk b) (IS stStreaming) (λ z → z) sv-IS-bdone (h b))
  where
  h : ∀ b → viewV (PTree.force (CB-blk b)) (ApiBFCar sendBFBatchDone , apiBF sendBFBatchDone) tt ≡ nothing
  h b = refl
im-W4-recv : ∀ b b′ → JP (CB-blk b) (SB-blk b′) ─[ ev (evRecv b) ]─► JP (CB-loop stStreaming) (SB-blk b′)
im-W4-recv b b′ = Hide-keep msgBF (Par msgBF mrg (CB-blk b) (SB-blk b′)) (λ z → z)
  (Par-soloL msgBF mrg (CB-blk b) (SB-blk b′) (λ z → z) (cl-CBblk-recv b) (no-SBblk-recv b′ b))
im-W5-recv : ∀ b → JP (CB-blk b) SB-bdone ─[ ev (evRecv b) ]─► JP (CB-loop stStreaming) SB-bdone
im-W5-recv b = Hide-keep msgBF (Par msgBF mrg (CB-blk b) SB-bdone) (λ z → z)
  (Par-soloL msgBF mrg (CB-blk b) SB-bdone (λ z → z) (cl-CBblk-recv b) (no-SBbdone-recv b))

------------------------------------------------------------------------
-- IMPL hidden-message sync τ steps (Hide-hidden of a Par-sync).
------------------------------------------------------------------------
-- client emits MsgRequestRange\!r ; server (IS idle) accepts → loop.
im-B-τ : ∀ r → JP (CB-req r) (IS stIdle) ─[ τ ]─► JP (CB-loop stBusy) (SB-req r)
im-B-τ r = Hide-hidden msgBF (Par msgBF mrg (CB-req r) (IS stIdle)) Poly.tt
  (Par-sync msgBF mrg (CB-req r) (IS stIdle) Poly.tt (sVis refl (hc r)) (sVis refl (hs r)))
  where
  hc : ∀ r → viewV (PTree.force (CB-req r)) (ChainRange , MsgRequestRange) r ≡ just (CB-loop stBusy)
  hc r rewrite ≟-diagR r = refl
  hs : ∀ r → viewV (PTree.force (IS stIdle)) (ChainRange , MsgRequestRange) r ≡ just (SB-req r)
  hs r = refl
-- client emits MsgClientDone ; server (IS idle) accepts → done loops.
im-C-τ : JP CB-cdone (IS stIdle) ─[ τ ]─► JP (CB-loop stDone) (SB-loop stDone)
im-C-τ = Hide-hidden msgBF (Par msgBF mrg CB-cdone (IS stIdle)) Poly.tt
  (Par-sync msgBF mrg CB-cdone (IS stIdle) Poly.tt (sVis refl refl) (sVis refl refl))
-- server emits MsgStartBatch ; client (IC busy) accepts → str loops.
im-M-τ : JP (IC stBusy) SB-sbatch ─[ τ ]─► JP (CB-loop stStreaming) (SB-loop stStreaming)
im-M-τ = Hide-hidden msgBF (Par msgBF mrg (IC stBusy) SB-sbatch) Poly.tt
  (Par-sync msgBF mrg (IC stBusy) SB-sbatch Poly.tt (sVis refl refl) (sVis refl refl))
-- server emits MsgNoBlocks ; client (IC busy) accepts → idle loops.
im-N-τ : JP (IC stBusy) SB-noblk ─[ τ ]─► JP (CB-loop stIdle) (SB-loop stIdle)
im-N-τ = Hide-hidden msgBF (Par msgBF mrg (IC stBusy) SB-noblk) Poly.tt
  (Par-sync msgBF mrg (IC stBusy) SB-noblk Poly.tt (sVis refl refl) (sVis refl refl))
-- server emits MsgBlock\!b ; client (IC str) accepts → (CB-blk b, loop str).
im-W-τ : ∀ b → JP (IC stStreaming) (SB-blk b) ─[ τ ]─► JP (CB-blk b) (SB-loop stStreaming)
im-W-τ b = Hide-hidden msgBF (Par msgBF mrg (IC stStreaming) (SB-blk b)) Poly.tt
  (Par-sync msgBF mrg (IC stStreaming) (SB-blk b) Poly.tt (sVis refl (hc b)) (sVis refl (hs b)))
  where
  hc : ∀ b → viewV (PTree.force (IC stStreaming)) (Block , MsgBlock) b ≡ just (CB-blk b)
  hc b = refl
  hs : ∀ b → viewV (PTree.force (SB-blk b)) (Block , MsgBlock) b ≡ just (SB-loop stStreaming)
  hs b rewrite ≟-diagB b = refl
-- server emits MsgBatchDone ; client (IC str) accepts → idle loops.
im-Y-τ : JP (IC stStreaming) SB-bdone ─[ τ ]─► JP (CB-loop stIdle) (SB-loop stIdle)
im-Y-τ = Hide-hidden msgBF (Par msgBF mrg (IC stStreaming) SB-bdone) Poly.tt
  (Par-sync msgBF mrg (IC stStreaming) SB-bdone Poly.tt (sVis refl refl) (sVis refl refl))

------------------------------------------------------------------------
-- IMPL iter loop-back τ steps (Hide-τ of a Par-τ with sSil).
------------------------------------------------------------------------
im-D-τ : ∀ r → JP (CB-loop stBusy) (SB-req r) ─[ τ ]─► JP (IC stBusy) (SB-req r)
im-D-τ r = Hide-τ msgBF (Par msgBF mrg (CB-loop stBusy) (SB-req r))
  (Par-τ-L msgBF mrg (CB-loop stBusy) (SB-req r) (sSil refl))
im-H-τ : JP (IC stBusy) (SB-loop stBusy) ─[ τ ]─► JP (IC stBusy) (IS stBusy)
im-H-τ = Hide-τ msgBF (Par msgBF mrg (IC stBusy) (SB-loop stBusy))
  (Par-τ-R msgBF mrg (IC stBusy) (SB-loop stBusy) (sSil refl))
im-R-τ : JP (IC stStreaming) (SB-loop stStreaming) ─[ τ ]─► JP (IC stStreaming) (IS stStreaming)
im-R-τ = Hide-τ msgBF (Par msgBF mrg (IC stStreaming) (SB-loop stStreaming))
  (Par-τ-R msgBF mrg (IC stStreaming) (SB-loop stStreaming) (sSil refl))
im-T-τ : JP (IC stIdle) (SB-loop stIdle) ─[ τ ]─► JP (IC stIdle) (IS stIdle)
im-T-τ = Hide-τ msgBF (Par msgBF mrg (IC stIdle) (SB-loop stIdle))
  (Par-τ-R msgBF mrg (IC stIdle) (SB-loop stIdle) (sSil refl))
im-U-τ : JP (CB-loop stIdle) (IS stIdle) ─[ τ ]─► JP (IC stIdle) (IS stIdle)
im-U-τ = Hide-τ msgBF (Par msgBF mrg (CB-loop stIdle) (IS stIdle))
  (Par-τ-L msgBF mrg (CB-loop stIdle) (IS stIdle) (sSil refl))
im-I-τ : JP (CB-loop stBusy) (IS stBusy) ─[ τ ]─► JP (IC stBusy) (IS stBusy)
im-I-τ = Hide-τ msgBF (Par msgBF mrg (CB-loop stBusy) (IS stBusy))
  (Par-τ-L msgBF mrg (CB-loop stBusy) (IS stBusy) (sSil refl))
im-S-τ : JP (CB-loop stStreaming) (IS stStreaming) ─[ τ ]─► JP (IC stStreaming) (IS stStreaming)
im-S-τ = Hide-τ msgBF (Par msgBF mrg (CB-loop stStreaming) (IS stStreaming))
  (Par-τ-L msgBF mrg (CB-loop stStreaming) (IS stStreaming) (sSil refl))
im-E1-τ : JP (IC stDone) (SB-loop stDone) ─[ τ ]─► JP (IC stDone) (IS stDone)
im-E1-τ = Hide-τ msgBF (Par msgBF mrg (IC stDone) (SB-loop stDone))
  (Par-τ-R msgBF mrg (IC stDone) (SB-loop stDone) (sSil refl))
im-E2-τ : JP (CB-loop stDone) (IS stDone) ─[ τ ]─► JP (IC stDone) (IS stDone)
im-E2-τ = Hide-τ msgBF (Par msgBF mrg (CB-loop stDone) (IS stDone))
  (Par-τ-L msgBF mrg (CB-loop stDone) (IS stDone) (sSil refl))
im-K-τ : JP (CB-loop stBusy) SB-sbatch ─[ τ ]─► JP (IC stBusy) SB-sbatch
im-K-τ = Hide-τ msgBF (Par msgBF mrg (CB-loop stBusy) SB-sbatch)
  (Par-τ-L msgBF mrg (CB-loop stBusy) SB-sbatch (sSil refl))
im-L-τ : JP (CB-loop stBusy) SB-noblk ─[ τ ]─► JP (IC stBusy) SB-noblk
im-L-τ = Hide-τ msgBF (Par msgBF mrg (CB-loop stBusy) SB-noblk)
  (Par-τ-L msgBF mrg (CB-loop stBusy) SB-noblk (sSil refl))
im-W2-τ : ∀ b → JP (CB-blk b) (SB-loop stStreaming) ─[ τ ]─► JP (CB-blk b) (IS stStreaming)
im-W2-τ b = Hide-τ msgBF (Par msgBF mrg (CB-blk b) (SB-loop stStreaming))
  (Par-τ-R msgBF mrg (CB-blk b) (SB-loop stStreaming) (sSil refl))
im-W6-τ : ∀ b → JP (CB-loop stStreaming) (SB-blk b) ─[ τ ]─► JP (IC stStreaming) (SB-blk b)
im-W6-τ b = Hide-τ msgBF (Par msgBF mrg (CB-loop stStreaming) (SB-blk b))
  (Par-τ-L msgBF mrg (CB-loop stStreaming) (SB-blk b) (sSil refl))
im-W7-τ : JP (CB-loop stStreaming) SB-bdone ─[ τ ]─► JP (IC stStreaming) SB-bdone
im-W7-τ = Hide-τ msgBF (Par msgBF mrg (CB-loop stStreaming) SB-bdone)
  (Par-τ-L msgBF mrg (CB-loop stStreaming) SB-bdone (sSil refl))
im-Ta-τ : ∀ r → JP (CB-req r) (SB-loop stIdle) ─[ τ ]─► JP (CB-req r) (IS stIdle)
im-Ta-τ r = Hide-τ msgBF (Par msgBF mrg (CB-req r) (SB-loop stIdle))
  (Par-τ-R msgBF mrg (CB-req r) (SB-loop stIdle) (sSil refl))
im-Tb-τ : JP CB-cdone (SB-loop stIdle) ─[ τ ]─► JP CB-cdone (IS stIdle)
im-Tb-τ = Hide-τ msgBF (Par msgBF mrg CB-cdone (SB-loop stIdle))
  (Par-τ-R msgBF mrg CB-cdone (SB-loop stIdle) (sSil refl))

------------------------------------------------------------------------
-- extra impl loop-back τ for bwd padding (reach the api-enabled twin).
im-G→I : JP (CB-loop stBusy) (SB-loop stBusy) ─[ τ ]─► JP (CB-loop stBusy) (IS stBusy)
im-G→I = Hide-τ msgBF (Par msgBF mrg (CB-loop stBusy) (SB-loop stBusy))
  (Par-τ-R msgBF mrg (CB-loop stBusy) (SB-loop stBusy) (sSil refl))
im-P→S : JP (CB-loop stStreaming) (SB-loop stStreaming) ─[ τ ]─► JP (CB-loop stStreaming) (IS stStreaming)
im-P→S = Hide-τ msgBF (Par msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming))
  (Par-τ-R msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming) (sSil refl))

-- more bwd-padding loop-back τ helpers.
im-E→E1 : JP (CB-loop stDone) (SB-loop stDone) ─[ τ ]─► JP (IC stDone) (SB-loop stDone)
im-E→E1 = Hide-τ msgBF (Par msgBF mrg (CB-loop stDone) (SB-loop stDone))
  (Par-τ-L msgBF mrg (CB-loop stDone) (SB-loop stDone) (sSil refl))
im-P→R : JP (CB-loop stStreaming) (SB-loop stStreaming) ─[ τ ]─► JP (IC stStreaming) (SB-loop stStreaming)
im-P→R = Hide-τ msgBF (Par msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming))
  (Par-τ-L msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming) (sSil refl))
im-Q→T : JP (CB-loop stIdle) (SB-loop stIdle) ─[ τ ]─► JP (IC stIdle) (SB-loop stIdle)
im-Q→T = Hide-τ msgBF (Par msgBF mrg (CB-loop stIdle) (SB-loop stIdle))
  (Par-τ-L msgBF mrg (CB-loop stIdle) (SB-loop stIdle) (sSil refl))

-- the coinductive bisimulation builder.
------------------------------------------------------------------------
-- deadlock ≈DR deadlock (both √-successors land here).
-- rsDL helpers: deadlock has no transitions, so every step is absurd.
rs_DL_fwd_ev : ∀ {l W′} → deadlock ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] ((deadlock) ═[ ev l ]═► S′ × RState W′ S′)
rs_DL_fwd_ev (sRet ())
rs_DL_fwd_ev (sVis refl ())
rs_DL_fwd_tau : ∀ {W′} → deadlock ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] ((deadlock) ═[ τ ]═► S′ × RState W′ S′)
rs_DL_fwd_tau (sSil ())
rs_DL_fwd_tau (sTau refl ())
rs_DL_bwd_ev : ∀ {l S′} → deadlock ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] ((deadlock) ═[ ev l ]═► W′ × RState W′ S′)
rs_DL_bwd_ev (sRet ())
rs_DL_bwd_ev (sVis refl ())
rs_DL_bwd_tau : ∀ {S′} → deadlock ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] ((deadlock) ═[ τ ]═► W′ × RState W′ S′)
rs_DL_bwd_tau (sSil ())
rs_DL_bwd_tau (sTau refl ())

------------------------------------------------------------------------
-- the coinductive bisimulation builders (guarded via data-returning step helpers).
------------------------------------------------------------------------
-- data-returning step helpers (the with-inversions live HERE, returning the
-- successor RState; the coinductive mkDR/mkDRˢ apply OUTSIDE any with, so the
-- corecursion stays guarded).
rs_A_fwd_ev : ∀ {l W′} → (JP (IC stIdle) (IS stIdle)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pIdle ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_A_fwd_ev st with Hide-ev-elim msgBF (Par msgBF mrg (IC stIdle) (IS stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stIdle) (IS stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 cstp (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 cstp (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} {a = aa} refl refl) =
          _ , wev τ*-refl (sp-pIdle-req aa) τ*-refl , (rsB aa)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) =
          _ , wev τ*-refl sp-pIdle-cdone τ*-refl , rsC
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_A_fwd_tau : ∀ {W′} → (JP (IC stIdle) (IS stIdle)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pIdle ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_A_fwd_tau st = ⊥-elim (A-noτ st)

rs_A_bwd_ev : ∀ {l S′} → (ITP pIdle ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stIdle) (IS stIdle))) ═[ ev l ]═► W′ × RState W′ S′)
rs_A_bwd_ev st with Hide-ev-elim msgBF (ITP pIdle) st
... | he√ ()
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} {a = aa} refl refl) =
        _ , wev τ*-refl (im-A-req aa) τ*-refl , (rsB aa)
... | heV {e = apiBF sendBFClientDone} P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) =
        _ , wev τ*-refl im-A-cdone τ*-refl , rsC
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
... | heV {e = apiBF sendBFNoBlocks} P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} refl ())
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} refl ())
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} refl ())
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch} P' ¬m (sVis {at = (_ , MsgStartBatch)} refl ())
... | heV {e = MsgNoBlocks} P' ¬m (sVis {at = (_ , MsgNoBlocks)} refl ())
... | heV {e = MsgBlock} P' ¬m (sVis {at = (_ , MsgBlock)} refl ())
... | heV {e = MsgBatchDone} P' ¬m (sVis {at = (_ , MsgBatchDone)} refl ())
... | heV {e = MsgClientDone} P' ¬m (sVis {at = (_ , MsgClientDone)} refl ())

rs_A_bwd_tau : ∀ {S′} → (ITP pIdle ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stIdle) (IS stIdle))) ═[ τ ]═► W′ × RState W′ S′)
rs_A_bwd_tau st = ⊥-elim (specP-noτ pIdle st)

rs_Z_fwd_ev : ∀ {l W′} → (JP (IC stDone) (IS stDone)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pDone ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_Z_fwd_ev st with Hide-ev-elim msgBF (Par msgBF mrg (IC stDone) (IS stDone)) st
... | he√ refl = _ , wev τ*-refl (Hide-√ msgBF (ITP pDone) refl) τ*-refl , rsDL
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stDone) (IS stDone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_Z_fwd_tau : ∀ {W′} → (JP (IC stDone) (IS stDone)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pDone ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_Z_fwd_tau st = ⊥-elim (Z-noτ st)

rs_Z_bwd_ev : ∀ {l S′} → (ITP pDone ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stDone) (IS stDone))) ═[ ev l ]═► W′ × RState W′ S′)
rs_Z_bwd_ev st with Hide-ev-elim msgBF (ITP pDone) st
... | he√ refl = _ , wev τ*-refl (Hide-√ msgBF (Par msgBF mrg (IC stDone) (IS stDone)) refl) τ*-refl , rsDL
... | heV P' ¬m (sVis () _)

rs_Z_bwd_tau : ∀ {S′} → (ITP pDone ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stDone) (IS stDone))) ═[ τ ]═► W′ × RState W′ S′)
rs_Z_bwd_tau st = ⊥-elim (specP-noτ pDone st)

rs_B_fwd_ev : (r : ChainRange) → ∀ {l W′} → (JP (CB-req r) (IS stIdle)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-req r ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_B_fwd_ev r st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-req r) (IS stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-req r) (IS stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_B_fwd_tau : (r : ChainRange) → ∀ {W′} → (JP (CB-req r) (IS stIdle)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-req r ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_B_fwd_tau r st with B-τ st
... | refl = _ , wτ (τ*-step (sp-Preq-τ r) τ*-refl) , (rsD r)

rs_B_bwd_ev : (r : ChainRange) → ∀ {l S′} → (P-req r ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-req r) (IS stIdle))) ═[ ev l ]═► W′ × RState W′ S′)
rs_B_bwd_ev r st with Hide-ev-elim msgBF (P-req r) st
... | heV {e = MsgRequestRange}          P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_B_bwd_tau : (r : ChainRange) → ∀ {S′} → (P-req r ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-req r) (IS stIdle))) ═[ τ ]═► W′ × RState W′ S′)
rs_B_bwd_tau r st with P-req-τ st
... | refl = _ , wτ (τ*-step (im-B-τ r) (τ*-refl)) , (rsD r)

rs_Ta_fwd_ev : (r : ChainRange) → ∀ {l W′} → (JP (CB-req r) (SB-loop stIdle)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-req r ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_Ta_fwd_ev r st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-req r) (SB-loop stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-req r) (SB-loop stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_Ta_fwd_tau : (r : ChainRange) → ∀ {W′} → (JP (CB-req r) (SB-loop stIdle)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-req r ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_Ta_fwd_tau r st with Ta-τ st
... | refl = _ , wτ τ*-refl , (rsB r)

rs_Ta_bwd_ev : (r : ChainRange) → ∀ {l S′} → (P-req r ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-req r) (SB-loop stIdle))) ═[ ev l ]═► W′ × RState W′ S′)
rs_Ta_bwd_ev r st with Hide-ev-elim msgBF (P-req r) st
... | heV {e = MsgRequestRange}          P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_Ta_bwd_tau : (r : ChainRange) → ∀ {S′} → (P-req r ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-req r) (SB-loop stIdle))) ═[ τ ]═► W′ × RState W′ S′)
rs_Ta_bwd_tau r st with P-req-τ st
... | refl = _ , wτ (τ*-step (im-Ta-τ r) (τ*-step (im-B-τ r) (τ*-refl))) , (rsD r)

rs_D_fwd_ev : (r : ChainRange) → ∀ {l W′} → (JP (CB-loop stBusy) (SB-req r)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-req2 r ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_D_fwd_ev r st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-req r)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-req r) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
rs_D_fwd_ev r st | heV P' ¬m pev | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl sbreq) with aa ≟ r
... | yes refl with sbreq
...   | refl = _ , wev τ*-refl (sp-preq2-reqR r) (τ*-step (sp-Ploop-τ pBusy) τ*-refl) , rsG
rs_D_fwd_ev r st | heV P' ¬m pev | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl ()) | no _

rs_D_fwd_tau : (r : ChainRange) → ∀ {W′} → (JP (CB-loop stBusy) (SB-req r)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-req2 r ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_D_fwd_tau r st with D-τ st
... | refl = _ , wτ τ*-refl , (rsF r)

rs_D_bwd_ev : (r : ChainRange) → ∀ {l S′} → (P-req2 r ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) (SB-req r))) ═[ ev l ]═► W′ × RState W′ S′)
rs_D_bwd_ev r st with Hide-ev-elim msgBF (P-req2 r) st
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl breq) with a ≟ r
...   | yes refl with breq
...     | refl = _ , wev (τ*-refl) (im-D-reqR r) (τ*-refl) , rsGp
rs_D_bwd_ev r st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl ()) | no _
rs_D_bwd_ev r st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_D_bwd_ev r st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
rs_D_bwd_ev r st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
rs_D_bwd_ev r st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
rs_D_bwd_ev r st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
rs_D_bwd_ev r st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
rs_D_bwd_ev r st | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
rs_D_bwd_ev r st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
rs_D_bwd_ev r st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
rs_D_bwd_ev r st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
rs_D_bwd_ev r st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
rs_D_bwd_ev r st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
rs_D_bwd_ev r st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
rs_D_bwd_ev r st | he√ ()

rs_D_bwd_tau : (r : ChainRange) → ∀ {S′} → (P-req2 r ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) (SB-req r))) ═[ τ ]═► W′ × RState W′ S′)
rs_D_bwd_tau r st = ⊥-elim (P-req2-noτ st)

rs_F_fwd_ev : (r : ChainRange) → ∀ {l W′} → (JP (IC stBusy) (SB-req r)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-req2 r ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_F_fwd_ev r st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-req r)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (SB-req r) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
rs_F_fwd_ev r st | heV P' ¬m pev | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl sbreq) with aa ≟ r
... | yes refl with sbreq
...   | refl = _ , wev τ*-refl (sp-preq2-reqR r) (τ*-step (sp-Ploop-τ pBusy) τ*-refl) , rsH
rs_F_fwd_ev r st | heV P' ¬m pev | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} {a = aa} refl ()) | no _

rs_F_fwd_tau : (r : ChainRange) → ∀ {W′} → (JP (IC stBusy) (SB-req r)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-req2 r ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_F_fwd_tau r st = ⊥-elim (F-noτ st)

rs_F_bwd_ev : (r : ChainRange) → ∀ {l S′} → (P-req2 r ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) (SB-req r))) ═[ ev l ]═► W′ × RState W′ S′)
rs_F_bwd_ev r st with Hide-ev-elim msgBF (P-req2 r) st
... | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl breq) with a ≟ r
...   | yes refl with breq
...     | refl = _ , wev (τ*-refl) (im-F-reqR r) (τ*-refl) , rsHp
rs_F_bwd_ev r st | heV {e = apiBF reqBFRange} P' ¬m (sVis {at = (_ , apiBF reqBFRange)} {a = a} refl ()) | no _
rs_F_bwd_ev r st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_F_bwd_ev r st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
rs_F_bwd_ev r st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
rs_F_bwd_ev r st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
rs_F_bwd_ev r st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
rs_F_bwd_ev r st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
rs_F_bwd_ev r st | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
rs_F_bwd_ev r st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
rs_F_bwd_ev r st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
rs_F_bwd_ev r st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
rs_F_bwd_ev r st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
rs_F_bwd_ev r st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
rs_F_bwd_ev r st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
rs_F_bwd_ev r st | he√ ()

rs_F_bwd_tau : (r : ChainRange) → ∀ {S′} → (P-req2 r ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) (SB-req r))) ═[ τ ]═► W′ × RState W′ S′)
rs_F_bwd_tau r st = ⊥-elim (P-req2-noτ st)

rs_C_fwd_ev : ∀ {l W′} → (JP CB-cdone (IS stIdle)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-cdone ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_C_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-cdone) (IS stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-cdone) (IS stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_C_fwd_tau : ∀ {W′} → (JP CB-cdone (IS stIdle)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-cdone ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_C_fwd_tau st with C-τ st
... | refl = _ , wτ (τ*-step sp-Pcdone-τ τ*-refl) , rsE

rs_C_bwd_ev : ∀ {l S′} → (P-cdone ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP CB-cdone (IS stIdle))) ═[ ev l ]═► W′ × RState W′ S′)
rs_C_bwd_ev st with Hide-ev-elim msgBF P-cdone st
... | heV {e = MsgClientDone}   P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_C_bwd_tau : ∀ {S′} → (P-cdone ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP CB-cdone (IS stIdle))) ═[ τ ]═► W′ × RState W′ S′)
rs_C_bwd_tau st with P-cdone-τ st
... | refl = _ , wτ (τ*-step (im-C-τ) (τ*-refl)) , rsE

rs_Tb_fwd_ev : ∀ {l W′} → (JP CB-cdone (SB-loop stIdle)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-cdone ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_Tb_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-cdone) (SB-loop stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-cdone) (SB-loop stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_Tb_fwd_tau : ∀ {W′} → (JP CB-cdone (SB-loop stIdle)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-cdone ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_Tb_fwd_tau st with Tb-τ st
... | refl = _ , wτ τ*-refl , rsC

rs_Tb_bwd_ev : ∀ {l S′} → (P-cdone ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP CB-cdone (SB-loop stIdle))) ═[ ev l ]═► W′ × RState W′ S′)
rs_Tb_bwd_ev st with Hide-ev-elim msgBF P-cdone st
... | heV {e = MsgClientDone}   P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_Tb_bwd_tau : ∀ {S′} → (P-cdone ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP CB-cdone (SB-loop stIdle))) ═[ τ ]═► W′ × RState W′ S′)
rs_Tb_bwd_tau st with P-cdone-τ st
... | refl = _ , wτ (τ*-step (im-Tb-τ) (τ*-step (im-C-τ) (τ*-refl))) , rsE

rs_E_fwd_ev : ∀ {l W′} → (JP (CB-loop stDone) (SB-loop stDone)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pDone ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_E_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stDone) (SB-loop stDone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stDone) (SB-loop stDone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_E_fwd_tau : ∀ {W′} → (JP (CB-loop stDone) (SB-loop stDone)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pDone ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_E_fwd_tau st with E-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsE1
... | inj₂ refl = _ , wτ τ*-refl , rsE2

rs_E_bwd_ev : ∀ {l S′} → (P-loop pDone ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stDone) (SB-loop stDone))) ═[ ev l ]═► W′ × RState W′ S′)
rs_E_bwd_ev st with Hide-ev-elim msgBF (P-loop pDone) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_E_bwd_tau : ∀ {S′} → (P-loop pDone ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stDone) (SB-loop stDone))) ═[ τ ]═► W′ × RState W′ S′)
rs_E_bwd_tau st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-E→E1) (τ*-step (im-E1-τ) (τ*-refl))) , rsZ

rs_E1_fwd_ev : ∀ {l W′} → (JP (IC stDone) (SB-loop stDone)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pDone ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_E1_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stDone) (SB-loop stDone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stDone) (SB-loop stDone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_E1_fwd_tau : ∀ {W′} → (JP (IC stDone) (SB-loop stDone)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pDone ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_E1_fwd_tau st with E1-τ st
... | refl = _ , wτ (τ*-step (sp-Ploop-τ pDone) τ*-refl) , rsZ

rs_E1_bwd_ev : ∀ {l S′} → (P-loop pDone ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stDone) (SB-loop stDone))) ═[ ev l ]═► W′ × RState W′ S′)
rs_E1_bwd_ev st with Hide-ev-elim msgBF (P-loop pDone) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_E1_bwd_tau : ∀ {S′} → (P-loop pDone ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stDone) (SB-loop stDone))) ═[ τ ]═► W′ × RState W′ S′)
rs_E1_bwd_tau st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-E1-τ) (τ*-refl)) , rsZ

rs_E2_fwd_ev : ∀ {l W′} → (JP (CB-loop stDone) (IS stDone)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pDone ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_E2_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stDone) (IS stDone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stDone) (IS stDone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_E2_fwd_tau : ∀ {W′} → (JP (CB-loop stDone) (IS stDone)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pDone ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_E2_fwd_tau st with E2-τ st
... | refl = _ , wτ (τ*-step (sp-Ploop-τ pDone) τ*-refl) , rsZ

rs_E2_bwd_ev : ∀ {l S′} → (P-loop pDone ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stDone) (IS stDone))) ═[ ev l ]═► W′ × RState W′ S′)
rs_E2_bwd_ev st with Hide-ev-elim msgBF (P-loop pDone) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_E2_bwd_tau : ∀ {S′} → (P-loop pDone ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stDone) (IS stDone))) ═[ τ ]═► W′ × RState W′ S′)
rs_E2_bwd_tau st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-E2-τ) (τ*-refl)) , rsZ

rs_G_fwd_ev : ∀ {l W′} → (JP (CB-loop stBusy) (SB-loop stBusy)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pBusy ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_G_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-loop stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-loop stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_G_fwd_tau : ∀ {W′} → (JP (CB-loop stBusy) (SB-loop stBusy)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pBusy ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_G_fwd_tau st with G-τ st
... | inj₁ refl = _ , wτ τ*-refl , rsH
... | inj₂ refl = _ , wτ τ*-refl , rsI

rs_G_bwd_ev : ∀ {l S′} → (ITP pBusy ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) (SB-loop stBusy))) ═[ ev l ]═► W′ × RState W′ S′)
rs_G_bwd_ev st with Hide-ev-elim msgBF (ITP pBusy) st
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = _ , wev (τ*-step (im-G→I) τ*-refl) (im-I-sbatch) (τ*-refl) , rsK
... | heV {e = apiBF sendBFNoBlocks}   P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}   refl refl) = _ , wev (τ*-step (im-G→I) τ*-refl) (im-I-noblk) (τ*-refl) , rsL
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()

rs_G_bwd_tau : ∀ {S′} → (ITP pBusy ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) (SB-loop stBusy))) ═[ τ ]═► W′ × RState W′ S′)
rs_G_bwd_tau st = ⊥-elim (specP-noτ pBusy st)

rs_H_fwd_ev : ∀ {l W′} → (JP (IC stBusy) (SB-loop stBusy)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pBusy ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_H_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-loop stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (SB-loop stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_H_fwd_tau : ∀ {W′} → (JP (IC stBusy) (SB-loop stBusy)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pBusy ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_H_fwd_tau st with H-τ st
... | refl = _ , wτ τ*-refl , rsJ

rs_H_bwd_ev : ∀ {l S′} → (ITP pBusy ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) (SB-loop stBusy))) ═[ ev l ]═► W′ × RState W′ S′)
rs_H_bwd_ev st with Hide-ev-elim msgBF (ITP pBusy) st
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = _ , wev (τ*-step (im-H-τ) τ*-refl) (im-J-sbatch) (τ*-refl) , rsM
... | heV {e = apiBF sendBFNoBlocks}   P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}   refl refl) = _ , wev (τ*-step (im-H-τ) τ*-refl) (im-J-noblk) (τ*-refl) , rsN
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()

rs_H_bwd_tau : ∀ {S′} → (ITP pBusy ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) (SB-loop stBusy))) ═[ τ ]═► W′ × RState W′ S′)
rs_H_bwd_tau st = ⊥-elim (specP-noτ pBusy st)

rs_I_fwd_ev : ∀ {l W′} → (JP (CB-loop stBusy) (IS stBusy)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pBusy ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_I_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (IS stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (IS stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = _ , wev τ*-refl (sp-pBusy-sbatch) τ*-refl , rsK
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl refl) = _ , wev τ*-refl (sp-pBusy-noblk) τ*-refl , rsL
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_I_fwd_tau : ∀ {W′} → (JP (CB-loop stBusy) (IS stBusy)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pBusy ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_I_fwd_tau st with I-τ st
... | refl = _ , wτ τ*-refl , rsJ

rs_I_bwd_ev : ∀ {l S′} → (ITP pBusy ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) (IS stBusy))) ═[ ev l ]═► W′ × RState W′ S′)
rs_I_bwd_ev st with Hide-ev-elim msgBF (ITP pBusy) st
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = _ , wev (τ*-refl) (im-I-sbatch) (τ*-refl) , rsK
... | heV {e = apiBF sendBFNoBlocks}   P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}   refl refl) = _ , wev (τ*-refl) (im-I-noblk) (τ*-refl) , rsL
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()

rs_I_bwd_tau : ∀ {S′} → (ITP pBusy ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) (IS stBusy))) ═[ τ ]═► W′ × RState W′ S′)
rs_I_bwd_tau st = ⊥-elim (specP-noτ pBusy st)

rs_J_fwd_ev : ∀ {l W′} → (JP (IC stBusy) (IS stBusy)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pBusy ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_J_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (IS stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (IS stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = _ , wev τ*-refl (sp-pBusy-sbatch) τ*-refl , rsM
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl refl) = _ , wev τ*-refl (sp-pBusy-noblk) τ*-refl , rsN
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_J_fwd_tau : ∀ {W′} → (JP (IC stBusy) (IS stBusy)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pBusy ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_J_fwd_tau st = ⊥-elim (J-noτ st)

rs_J_bwd_ev : ∀ {l S′} → (ITP pBusy ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) (IS stBusy))) ═[ ev l ]═► W′ × RState W′ S′)
rs_J_bwd_ev st with Hide-ev-elim msgBF (ITP pBusy) st
... | heV {e = apiBF sendBFStartBatch} P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)} refl refl) = _ , wev (τ*-refl) (im-J-sbatch) (τ*-refl) , rsM
... | heV {e = apiBF sendBFNoBlocks}   P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}   refl refl) = _ , wev (τ*-refl) (im-J-noblk) (τ*-refl) , rsN
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()

rs_J_bwd_tau : ∀ {S′} → (ITP pBusy ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) (IS stBusy))) ═[ τ ]═► W′ × RState W′ S′)
rs_J_bwd_tau st = ⊥-elim (specP-noτ pBusy st)

rs_K_fwd_ev : ∀ {l W′} → (JP (CB-loop stBusy) SB-sbatch) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-sbatch ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_K_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-sbatch)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-sbatch) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_K_fwd_tau : ∀ {W′} → (JP (CB-loop stBusy) SB-sbatch) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-sbatch ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_K_fwd_tau st with K-τ st
... | refl = _ , wτ τ*-refl , rsM

rs_K_bwd_ev : ∀ {l S′} → (P-sbatch ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) SB-sbatch)) ═[ ev l ]═► W′ × RState W′ S′)
rs_K_bwd_ev st with Hide-ev-elim msgBF P-sbatch st
... | heV {e = MsgStartBatch}   P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_K_bwd_tau : ∀ {S′} → (P-sbatch ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) SB-sbatch)) ═[ τ ]═► W′ × RState W′ S′)
rs_K_bwd_tau st with P-sbatch-τ st
... | refl = _ , wτ (τ*-step (im-K-τ) (τ*-step (im-M-τ) (τ*-refl))) , rsP

rs_L_fwd_ev : ∀ {l W′} → (JP (CB-loop stBusy) SB-noblk) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-noblk ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_L_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-noblk)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-noblk) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_L_fwd_tau : ∀ {W′} → (JP (CB-loop stBusy) SB-noblk) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-noblk ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_L_fwd_tau st with L-τ st
... | refl = _ , wτ τ*-refl , rsN

rs_L_bwd_ev : ∀ {l S′} → (P-noblk ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) SB-noblk)) ═[ ev l ]═► W′ × RState W′ S′)
rs_L_bwd_ev st with Hide-ev-elim msgBF P-noblk st
... | heV {e = MsgNoBlocks}     P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_L_bwd_tau : ∀ {S′} → (P-noblk ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) SB-noblk)) ═[ τ ]═► W′ × RState W′ S′)
rs_L_bwd_tau st with P-noblk-τ st
... | refl = _ , wτ (τ*-step (im-L-τ) (τ*-step (im-N-τ) (τ*-refl))) , rsQ

rs_M_fwd_ev : ∀ {l W′} → (JP (IC stBusy) SB-sbatch) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-sbatch ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_M_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-sbatch)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (SB-sbatch) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_M_fwd_tau : ∀ {W′} → (JP (IC stBusy) SB-sbatch) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-sbatch ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_M_fwd_tau st with M-τ st
... | refl = _ , wτ (τ*-step sp-Psbatch-τ τ*-refl) , rsP

rs_M_bwd_ev : ∀ {l S′} → (P-sbatch ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) SB-sbatch)) ═[ ev l ]═► W′ × RState W′ S′)
rs_M_bwd_ev st with Hide-ev-elim msgBF P-sbatch st
... | heV {e = MsgStartBatch}   P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_M_bwd_tau : ∀ {S′} → (P-sbatch ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) SB-sbatch)) ═[ τ ]═► W′ × RState W′ S′)
rs_M_bwd_tau st with P-sbatch-τ st
... | refl = _ , wτ (τ*-step (im-M-τ) (τ*-refl)) , rsP

rs_N_fwd_ev : ∀ {l W′} → (JP (IC stBusy) SB-noblk) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-noblk ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_N_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-noblk)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (SB-noblk) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_N_fwd_tau : ∀ {W′} → (JP (IC stBusy) SB-noblk) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-noblk ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_N_fwd_tau st with N-τ st
... | refl = _ , wτ (τ*-step sp-Pnoblk-τ τ*-refl) , rsQ

rs_N_bwd_ev : ∀ {l S′} → (P-noblk ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) SB-noblk)) ═[ ev l ]═► W′ × RState W′ S′)
rs_N_bwd_ev st with Hide-ev-elim msgBF P-noblk st
... | heV {e = MsgNoBlocks}     P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgBatchDone}    P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_N_bwd_tau : ∀ {S′} → (P-noblk ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) SB-noblk)) ═[ τ ]═► W′ × RState W′ S′)
rs_N_bwd_tau st with P-noblk-τ st
... | refl = _ , wτ (τ*-step (im-N-τ) (τ*-refl)) , rsQ

rs_P_fwd_ev : ∀ {l W′} → (JP (CB-loop stStreaming) (SB-loop stStreaming)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pStr0 ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_P_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-loop stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_P_fwd_tau : ∀ {W′} → (JP (CB-loop stStreaming) (SB-loop stStreaming)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pStr0 ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_P_fwd_tau st with P-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Ploop-τ pStr0) τ*-refl) , rsR
... | inj₂ refl = _ , wτ (τ*-step (sp-Ploop-τ pStr0) τ*-refl) , rsS

rs_P_bwd_ev : ∀ {l S′} → (P-loop pStr0 ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (SB-loop stStreaming))) ═[ ev l ]═► W′ × RState W′ S′)
rs_P_bwd_ev st with Hide-ev-elim msgBF (P-loop pStr0) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_P_bwd_tau : ∀ {S′} → (P-loop pStr0 ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (SB-loop stStreaming))) ═[ τ ]═► W′ × RState W′ S′)
rs_P_bwd_tau st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-P→R) (τ*-refl)) , rsR

rs_Q_fwd_ev : ∀ {l W′} → (JP (CB-loop stIdle) (SB-loop stIdle)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pIdle ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_Q_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stIdle) (SB-loop stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stIdle) (SB-loop stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_Q_fwd_tau : ∀ {W′} → (JP (CB-loop stIdle) (SB-loop stIdle)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pIdle ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_Q_fwd_tau st with Q-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Ploop-τ pIdle) τ*-refl) , rsT
... | inj₂ refl = _ , wτ τ*-refl , rsU

rs_Q_bwd_ev : ∀ {l S′} → (P-loop pIdle ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stIdle) (SB-loop stIdle))) ═[ ev l ]═► W′ × RState W′ S′)
rs_Q_bwd_ev st with Hide-ev-elim msgBF (P-loop pIdle) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_Q_bwd_tau : ∀ {S′} → (P-loop pIdle ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stIdle) (SB-loop stIdle))) ═[ τ ]═► W′ × RState W′ S′)
rs_Q_bwd_tau st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-Q→T) (τ*-refl)) , rsT

rs_R_fwd_ev : ∀ {l W′} → (JP (IC stStreaming) (SB-loop stStreaming)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pStr0 ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_R_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (SB-loop stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stStreaming) (SB-loop stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_R_fwd_tau : ∀ {W′} → (JP (IC stStreaming) (SB-loop stStreaming)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pStr0 ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_R_fwd_tau st with R-τ st
... | refl = _ , wτ τ*-refl , rsV

rs_R_bwd_ev : ∀ {l S′} → (ITP pStr0 ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) (SB-loop stStreaming))) ═[ ev l ]═► W′ × RState W′ S′)
rs_R_bwd_ev st with Hide-ev-elim msgBF (ITP pStr0) st
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = _ , wev (τ*-step (im-R-τ) τ*-refl) (im-V-blk b) (τ*-refl) , (rsW b)
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-step (im-R-τ) τ*-refl) (im-V-bdone) (τ*-refl) , rsY
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()

rs_R_bwd_tau : ∀ {S′} → (ITP pStr0 ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) (SB-loop stStreaming))) ═[ τ ]═► W′ × RState W′ S′)
rs_R_bwd_tau st = ⊥-elim (specP-noτ pStr0 st)

rs_S_fwd_ev : ∀ {l W′} → (JP (CB-loop stStreaming) (IS stStreaming)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pStr0 ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_S_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (IS stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (IS stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} {a = aa} refl refl) = _ , wev τ*-refl (sp-pStr0-blk aa) τ*-refl , (rsW6 aa)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (sp-pStr0-bdone) τ*-refl , rsW7
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_S_fwd_tau : ∀ {W′} → (JP (CB-loop stStreaming) (IS stStreaming)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pStr0 ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_S_fwd_tau st with S-τ st
... | refl = _ , wτ τ*-refl , rsV

rs_S_bwd_ev : ∀ {l S′} → (ITP pStr0 ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (IS stStreaming))) ═[ ev l ]═► W′ × RState W′ S′)
rs_S_bwd_ev st with Hide-ev-elim msgBF (ITP pStr0) st
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = _ , wev (τ*-refl) (im-S-blk b) (τ*-refl) , (rsW6 b)
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-refl) (im-S-bdone) (τ*-refl) , rsW7
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()

rs_S_bwd_tau : ∀ {S′} → (ITP pStr0 ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (IS stStreaming))) ═[ τ ]═► W′ × RState W′ S′)
rs_S_bwd_tau st = ⊥-elim (specP-noτ pStr0 st)

rs_T_fwd_ev : ∀ {l W′} → (JP (IC stIdle) (SB-loop stIdle)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pIdle ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_T_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stIdle) (SB-loop stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stIdle) (SB-loop stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 cstp (sVis () _)
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 cstp (sVis () _)
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} {a = aa} refl refl) = _ , wev τ*-refl (sp-pIdle-req aa) τ*-refl , (rsTa aa)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl refl) = _ , wev τ*-refl (sp-pIdle-cdone) τ*-refl , rsTb
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_T_fwd_tau : ∀ {W′} → (JP (IC stIdle) (SB-loop stIdle)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pIdle ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_T_fwd_tau st with T-τ st
... | refl = _ , wτ τ*-refl , rsA

rs_T_bwd_ev : ∀ {l S′} → (ITP pIdle ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stIdle) (SB-loop stIdle))) ═[ ev l ]═► W′ × RState W′ S′)
rs_T_bwd_ev st with Hide-ev-elim msgBF (ITP pIdle) st
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} {a = r} refl refl) = _ , wev (τ*-refl) (im-T-req r) (τ*-refl) , (rsTa r)
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl refl) = _ , wev (τ*-refl) (im-T-cdone) (τ*-refl) , rsTb
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
... | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()

rs_T_bwd_tau : ∀ {S′} → (ITP pIdle ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stIdle) (SB-loop stIdle))) ═[ τ ]═► W′ × RState W′ S′)
rs_T_bwd_tau st = ⊥-elim (specP-noτ pIdle st)

rs_U_fwd_ev : ∀ {l W′} → (JP (CB-loop stIdle) (IS stIdle)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pIdle ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_U_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stIdle) (IS stIdle)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stIdle) (IS stIdle) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_U_fwd_tau : ∀ {W′} → (JP (CB-loop stIdle) (IS stIdle)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pIdle ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_U_fwd_tau st with U-τ st
... | refl = _ , wτ (τ*-step (sp-Ploop-τ pIdle) τ*-refl) , rsA

rs_U_bwd_ev : ∀ {l S′} → (P-loop pIdle ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stIdle) (IS stIdle))) ═[ ev l ]═► W′ × RState W′ S′)
rs_U_bwd_ev st with Hide-ev-elim msgBF (P-loop pIdle) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_U_bwd_tau : ∀ {S′} → (P-loop pIdle ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stIdle) (IS stIdle))) ═[ τ ]═► W′ × RState W′ S′)
rs_U_bwd_tau st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-U-τ) (τ*-refl)) , rsA

rs_V_fwd_ev : ∀ {l W′} → (JP (IC stStreaming) (IS stStreaming)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pStr0 ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_V_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (IS stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stStreaming) (IS stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} {a = aa} refl refl) = _ , wev τ*-refl (sp-pStr0-blk aa) τ*-refl , (rsW aa)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (sp-pStr0-bdone) τ*-refl , rsY
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_V_fwd_tau : ∀ {W′} → (JP (IC stStreaming) (IS stStreaming)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP pStr0 ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_V_fwd_tau st = ⊥-elim (V-noτ st)

rs_V_bwd_ev : ∀ {l S′} → (ITP pStr0 ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) (IS stStreaming))) ═[ ev l ]═► W′ × RState W′ S′)
rs_V_bwd_ev st with Hide-ev-elim msgBF (ITP pStr0) st
... | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b} refl refl) = _ , wev (τ*-refl) (im-V-blk b) (τ*-refl) , (rsW b)
... | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-refl) (im-V-bdone) (τ*-refl) , rsY
... | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
... | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
... | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
... | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
... | heV {e = apiBF recvBFBlock}        P' ¬m (sVis {at = (_ , apiBF recvBFBlock)}        refl ())
... | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
... | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
... | he√ ()

rs_V_bwd_tau : ∀ {S′} → (ITP pStr0 ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) (IS stStreaming))) ═[ τ ]═► W′ × RState W′ S′)
rs_V_bwd_tau st = ⊥-elim (specP-noτ pStr0 st)

rs_W_fwd_ev : (b : Block) → ∀ {l W′} → (JP (IC stStreaming) (SB-blk b)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-blk0 b ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W_fwd_ev b st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (SB-blk b)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stStreaming) (SB-blk b) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_W_fwd_tau : (b : Block) → ∀ {W′} → (JP (IC stStreaming) (SB-blk b)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-blk0 b ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W_fwd_tau b st with W-τ st
... | refl = _ , wτ (τ*-step (sp-Pblk0-τ b) τ*-refl) , (rsW2 b)

rs_W_bwd_ev : (b : Block) → ∀ {l S′} → (P-blk0 b ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) (SB-blk b))) ═[ ev l ]═► W′ × RState W′ S′)
rs_W_bwd_ev b st with Hide-ev-elim msgBF (P-blk0 b) st
... | heV {e = MsgBlock}                 P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_W_bwd_tau : (b : Block) → ∀ {S′} → (P-blk0 b ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) (SB-blk b))) ═[ τ ]═► W′ × RState W′ S′)
rs_W_bwd_tau b st with P-blk0-τ st
... | refl = _ , wτ (τ*-step (im-W-τ b) (τ*-refl)) , (rsW2 b)

rs_W2_fwd_ev : (b : Block) → ∀ {l W′} → (JP (CB-blk b) (SB-loop stStreaming)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop (pStr1 b) ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W2_fwd_ev b st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-loop stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (SB-loop stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis () _)
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
rs_W2_fwd_ev b st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = _ , wev (τ*-step (sp-Ploop-τ (pStr1 b)) τ*-refl) (sp-pStr1-recv b) τ*-refl , rsP
rs_W2_fwd_ev b st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _

rs_W2_fwd_tau : (b : Block) → ∀ {W′} → (JP (CB-blk b) (SB-loop stStreaming)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop (pStr1 b) ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W2_fwd_tau b st with W2-τ st
... | refl = _ , wτ (τ*-step (sp-Ploop-τ (pStr1 b)) τ*-refl) , (rsW3 b)

rs_W2_bwd_ev : (b : Block) → ∀ {l S′} → (P-loop (pStr1 b) ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (SB-loop stStreaming))) ═[ ev l ]═► W′ × RState W′ S′)
rs_W2_bwd_ev b st with Hide-ev-elim msgBF (P-loop (pStr1 b)) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_W2_bwd_tau : (b : Block) → ∀ {S′} → (P-loop (pStr1 b) ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (SB-loop stStreaming))) ═[ τ ]═► W′ × RState W′ S′)
rs_W2_bwd_tau b st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-W2-τ b) (τ*-refl)) , (rsW3 b)

rs_W3_fwd_ev : (b : Block) → ∀ {l W′} → (JP (CB-blk b) (IS stStreaming)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP (pStr1 b) ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W3_fwd_ev b st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (IS stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (IS stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} {a = aa} refl refl) = _ , wev τ*-refl (sp-pStr1-blk b aa) (τ*-step (sp-PblkP-τ b aa) (τ*-step (sp-Ploop-τ (pStr2 b aa)) τ*-refl)) , (rsW4 b aa)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev τ*-refl (sp-pStr1-bdone b) (τ*-step (sp-Ploop-τ (pStrD b)) τ*-refl) , (rsW5 b)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
rs_W3_fwd_ev b st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = _ , wev τ*-refl (sp-pStr1-recv b) τ*-refl , rsS′
rs_W3_fwd_ev b st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _

rs_W3_fwd_tau : (b : Block) → ∀ {W′} → (JP (CB-blk b) (IS stStreaming)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP (pStr1 b) ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W3_fwd_tau b st = ⊥-elim (W3-noτ st)

rs_W3_bwd_ev : (b : Block) → ∀ {l S′} → (ITP (pStr1 b) ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (IS stStreaming))) ═[ ev l ]═► W′ × RState W′ S′)
rs_W3_bwd_ev b st with Hide-ev-elim msgBF (ITP (pStr1 b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl breq) with b ≟ x
...   | yes refl with breq
...     | refl = _ , wev (τ*-refl) (im-W3-recv b) (τ*-refl) , rsS′
rs_W3_bwd_ev b st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = x} refl ()) | no _
rs_W3_bwd_ev b st | heV {e = apiBF sendBFBlock} P' ¬m (sVis {at = (_ , apiBF sendBFBlock)} {a = b′} refl refl) = _ , wev (τ*-refl) (im-W3-blk b b′) (τ*-refl) , (rsW4p b b′)
rs_W3_bwd_ev b st | heV {e = apiBF sendBFBatchDone} P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-refl) (im-W3-bdone b) (τ*-refl) , (rsW5q b)
rs_W3_bwd_ev b st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W3_bwd_ev b st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
rs_W3_bwd_ev b st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
rs_W3_bwd_ev b st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
rs_W3_bwd_ev b st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
rs_W3_bwd_ev b st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
rs_W3_bwd_ev b st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
rs_W3_bwd_ev b st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
rs_W3_bwd_ev b st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
rs_W3_bwd_ev b st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
rs_W3_bwd_ev b st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
rs_W3_bwd_ev b st | he√ ()

rs_W3_bwd_tau : (b : Block) → ∀ {S′} → (ITP (pStr1 b) ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (IS stStreaming))) ═[ τ ]═► W′ × RState W′ S′)
rs_W3_bwd_tau b st = ⊥-elim (specP-noτ (pStr1 b) st)

rs_W4_fwd_ev : (b b′ : Block) → ∀ {l W′} → (JP (CB-blk b) (SB-blk b′)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP (pStr2 b b′) ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W4_fwd_ev b b′ st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-blk b′)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (SB-blk b′) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
rs_W4_fwd_ev b b′ st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = _ , wev τ*-refl (sp-pStr2-recv b b′) τ*-refl , (rsW6′ b′)
rs_W4_fwd_ev b b′ st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _

rs_W4_fwd_tau : (b b′ : Block) → ∀ {W′} → (JP (CB-blk b) (SB-blk b′)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP (pStr2 b b′) ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W4_fwd_tau b b′ st = ⊥-elim (W4-noτ st)

rs_W4_bwd_ev : (b b′ : Block) → ∀ {l S′} → (ITP (pStr2 b b′) ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (SB-blk b′))) ═[ ev l ]═► W′ × RState W′ S′)
rs_W4_bwd_ev b b′ st with Hide-ev-elim msgBF (ITP (pStr2 b b′)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl breq) with a ≟ b
...   | yes refl with breq
...     | refl = _ , wev (τ*-refl) (im-W4-recv b b′) (τ*-refl) , (rsW6′ b′)
rs_W4_bwd_ev b b′ st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl ()) | no _
rs_W4_bwd_ev b b′ st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W4_bwd_ev b b′ st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
rs_W4_bwd_ev b b′ st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
rs_W4_bwd_ev b b′ st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
rs_W4_bwd_ev b b′ st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
rs_W4_bwd_ev b b′ st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
rs_W4_bwd_ev b b′ st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
rs_W4_bwd_ev b b′ st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
rs_W4_bwd_ev b b′ st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
rs_W4_bwd_ev b b′ st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
rs_W4_bwd_ev b b′ st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
rs_W4_bwd_ev b b′ st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
rs_W4_bwd_ev b b′ st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
rs_W4_bwd_ev b b′ st | he√ ()

rs_W4_bwd_tau : (b b′ : Block) → ∀ {S′} → (ITP (pStr2 b b′) ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (SB-blk b′))) ═[ τ ]═► W′ × RState W′ S′)
rs_W4_bwd_tau b b′ st = ⊥-elim (specP-noτ (pStr2 b b′) st)

rs_W5_fwd_ev : (b : Block) → ∀ {l W′} → (JP (CB-blk b) SB-bdone) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP (pStrD b) ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W5_fwd_ev b st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-bdone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (SB-bdone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
rs_W5_fwd_ev b st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = _ , wev τ*-refl (sp-pStrD-recv b) τ*-refl , rsW7
rs_W5_fwd_ev b st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _

rs_W5_fwd_tau : (b : Block) → ∀ {W′} → (JP (CB-blk b) SB-bdone) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((ITP (pStrD b) ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W5_fwd_tau b st = ⊥-elim (W5-noτ st)

rs_W5_bwd_ev : (b : Block) → ∀ {l S′} → (ITP (pStrD b) ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) SB-bdone)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W5_bwd_ev b st with Hide-ev-elim msgBF (ITP (pStrD b)) st
... | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl breq) with a ≟ b
...   | yes refl with breq
...     | refl = _ , wev (τ*-refl) (im-W5-recv b) (τ*-refl) , rsW7
rs_W5_bwd_ev b st | heV {e = apiBF recvBFBlock} P' ¬m (sVis {at = (_ , apiBF recvBFBlock)} {a = a} refl ()) | no _
rs_W5_bwd_ev b st | heV {e = apiBF sendBFRequestRange} P' ¬m (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
rs_W5_bwd_ev b st | heV {e = apiBF sendBFClientDone}   P' ¬m (sVis {at = (_ , apiBF sendBFClientDone)}   refl ())
rs_W5_bwd_ev b st | heV {e = apiBF sendBFStartBatch}   P' ¬m (sVis {at = (_ , apiBF sendBFStartBatch)}   refl ())
rs_W5_bwd_ev b st | heV {e = apiBF sendBFNoBlocks}     P' ¬m (sVis {at = (_ , apiBF sendBFNoBlocks)}     refl ())
rs_W5_bwd_ev b st | heV {e = apiBF sendBFBlock}        P' ¬m (sVis {at = (_ , apiBF sendBFBlock)}        refl ())
rs_W5_bwd_ev b st | heV {e = apiBF sendBFBatchDone}    P' ¬m (sVis {at = (_ , apiBF sendBFBatchDone)}    refl ())
rs_W5_bwd_ev b st | heV {e = apiBF reqBFRange}         P' ¬m (sVis {at = (_ , apiBF reqBFRange)}         refl ())
rs_W5_bwd_ev b st | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)}          refl ())
rs_W5_bwd_ev b st | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}            refl ())
rs_W5_bwd_ev b st | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}              refl ())
rs_W5_bwd_ev b st | heV {e = MsgBlock}                 P' ¬m (sVis {at = (_ , MsgBlock)}                 refl ())
rs_W5_bwd_ev b st | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}             refl ())
rs_W5_bwd_ev b st | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}            refl ())
rs_W5_bwd_ev b st | he√ ()

rs_W5_bwd_tau : (b : Block) → ∀ {S′} → (ITP (pStrD b) ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) SB-bdone)) ═[ τ ]═► W′ × RState W′ S′)
rs_W5_bwd_tau b st = ⊥-elim (specP-noτ (pStrD b) st)

rs_W6_fwd_ev : (b : Block) → ∀ {l W′} → (JP (CB-loop stStreaming) (SB-blk b)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-blk0 b ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W6_fwd_ev b st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-blk b)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-blk b) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_W6_fwd_tau : (b : Block) → ∀ {W′} → (JP (CB-loop stStreaming) (SB-blk b)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-blk0 b ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W6_fwd_tau b st with W6-τ st
... | refl = _ , wτ τ*-refl , (rsW b)

rs_W6_bwd_ev : (b : Block) → ∀ {l S′} → (P-blk0 b ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (SB-blk b))) ═[ ev l ]═► W′ × RState W′ S′)
rs_W6_bwd_ev b st with Hide-ev-elim msgBF (P-blk0 b) st
... | heV {e = MsgBlock}                 P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_W6_bwd_tau : (b : Block) → ∀ {S′} → (P-blk0 b ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (SB-blk b))) ═[ τ ]═► W′ × RState W′ S′)
rs_W6_bwd_tau b st with P-blk0-τ st
... | refl = _ , wτ (τ*-step (im-W6-τ b) (τ*-step (im-W-τ b) (τ*-refl))) , (rsW2 b)

rs_W7_fwd_ev : ∀ {l W′} → (JP (CB-loop stStreaming) SB-bdone) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-bdone ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W7_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-bdone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-bdone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_W7_fwd_tau : ∀ {W′} → (JP (CB-loop stStreaming) SB-bdone) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-bdone ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W7_fwd_tau st with W7-τ st
... | refl = _ , wτ τ*-refl , rsY

rs_W7_bwd_ev : ∀ {l S′} → (P-bdone ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) SB-bdone)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W7_bwd_ev st with Hide-ev-elim msgBF P-bdone st
... | heV {e = MsgBatchDone}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_W7_bwd_tau : ∀ {S′} → (P-bdone ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) SB-bdone)) ═[ τ ]═► W′ × RState W′ S′)
rs_W7_bwd_tau st with P-bdone-τ st
... | refl = _ , wτ (τ*-step (im-W7-τ) (τ*-step (im-Y-τ) (τ*-refl))) , rsQ

rs_Y_fwd_ev : ∀ {l W′} → (JP (IC stStreaming) SB-bdone) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-bdone ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_Y_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (SB-bdone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stStreaming) (SB-bdone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_Y_fwd_tau : ∀ {W′} → (JP (IC stStreaming) SB-bdone) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-bdone ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_Y_fwd_tau st with Y-τ st
... | refl = _ , wτ (τ*-step sp-Pbdone-τ τ*-refl) , rsQ

rs_Y_bwd_ev : ∀ {l S′} → (P-bdone ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) SB-bdone)) ═[ ev l ]═► W′ × RState W′ S′)
rs_Y_bwd_ev st with Hide-ev-elim msgBF P-bdone st
... | heV {e = MsgBatchDone}    P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange} P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}   P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}     P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBlock}        P' ¬m (sVis {at = (_ , MsgBlock)}        refl ())
... | heV {e = MsgClientDone}   P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}         P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_Y_bwd_tau : ∀ {S′} → (P-bdone ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) SB-bdone)) ═[ τ ]═► W′ × RState W′ S′)
rs_Y_bwd_tau st with P-bdone-τ st
... | refl = _ , wτ (τ*-step (im-Y-τ) (τ*-refl)) , rsQ

rs_Gp_fwd_ev : ∀ {l W′} → (JP (CB-loop stBusy) (SB-loop stBusy)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pBusy ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_Gp_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stBusy) (SB-loop stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stBusy) (SB-loop stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_Gp_fwd_tau : ∀ {W′} → (JP (CB-loop stBusy) (SB-loop stBusy)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pBusy ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_Gp_fwd_tau st with G-τ st
... | inj₁ refl = _ , wτ (τ*-step (sp-Ploop-τ pBusy) τ*-refl) , rsH
... | inj₂ refl = _ , wτ (τ*-step (sp-Ploop-τ pBusy) τ*-refl) , rsI

rs_Gp_bwd_ev : ∀ {l S′} → (P-loop pBusy ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) (SB-loop stBusy))) ═[ ev l ]═► W′ × RState W′ S′)
rs_Gp_bwd_ev st with Hide-ev-elim msgBF (P-loop pBusy) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_Gp_bwd_tau : ∀ {S′} → (P-loop pBusy ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stBusy) (SB-loop stBusy))) ═[ τ ]═► W′ × RState W′ S′)
rs_Gp_bwd_tau st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-G→I) τ*-refl) , rsI

rs_Hp_fwd_ev : ∀ {l W′} → (JP (IC stBusy) (SB-loop stBusy)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pBusy ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_Hp_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stBusy) (SB-loop stBusy)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stBusy) (SB-loop stBusy) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_Hp_fwd_tau : ∀ {W′} → (JP (IC stBusy) (SB-loop stBusy)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pBusy ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_Hp_fwd_tau st with H-τ st
... | refl = _ , wτ (τ*-step (sp-Ploop-τ pBusy) τ*-refl) , rsJ

rs_Hp_bwd_ev : ∀ {l S′} → (P-loop pBusy ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) (SB-loop stBusy))) ═[ ev l ]═► W′ × RState W′ S′)
rs_Hp_bwd_ev st with Hide-ev-elim msgBF (P-loop pBusy) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_Hp_bwd_tau : ∀ {S′} → (P-loop pBusy ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stBusy) (SB-loop stBusy))) ═[ τ ]═► W′ × RState W′ S′)
rs_Hp_bwd_tau st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-H-τ) τ*-refl) , rsJ

rs_Wp_fwd_ev : (b : Block) → ∀ {l W′} → (JP (IC stStreaming) (SB-blk b)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop (pStr1 b) ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_Wp_fwd_ev b st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (IC stStreaming) (SB-blk b)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (IC stStreaming) (SB-blk b) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_Wp_fwd_tau : (b : Block) → ∀ {W′} → (JP (IC stStreaming) (SB-blk b)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop (pStr1 b) ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_Wp_fwd_tau b st with W-τ st
... | refl = _ , wτ τ*-refl , (rsW2 b)

rs_Wp_bwd_ev : (b : Block) → ∀ {l S′} → (P-loop (pStr1 b) ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) (SB-blk b))) ═[ ev l ]═► W′ × RState W′ S′)
rs_Wp_bwd_ev b st with Hide-ev-elim msgBF (P-loop (pStr1 b)) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_Wp_bwd_tau : (b : Block) → ∀ {S′} → (P-loop (pStr1 b) ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (IC stStreaming) (SB-blk b))) ═[ τ ]═► W′ × RState W′ S′)
rs_Wp_bwd_tau b st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-W-τ b) (τ*-step (im-W2-τ b) τ*-refl)) , (rsW3 b)

rs_Sp_fwd_ev : ∀ {l W′} → (JP (CB-loop stStreaming) (IS stStreaming)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pStr0 ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_Sp_fwd_ev st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (IS stStreaming)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (IS stStreaming) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} {a = aa} refl refl) = _ , wev (τ*-step (sp-Ploop-τ pStr0) τ*-refl) (sp-pStr0-blk aa) τ*-refl , (rsW6 aa)
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl refl) = _ , wev (τ*-step (sp-Ploop-τ pStr0) τ*-refl) (sp-pStr0-bdone) τ*-refl , rsW7
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_Sp_fwd_tau : ∀ {W′} → (JP (CB-loop stStreaming) (IS stStreaming)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop pStr0 ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_Sp_fwd_tau st with S-τ st
... | refl = _ , wτ (τ*-step (sp-Ploop-τ pStr0) τ*-refl) , rsV

rs_Sp_bwd_ev : ∀ {l S′} → (P-loop pStr0 ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (IS stStreaming))) ═[ ev l ]═► W′ × RState W′ S′)
rs_Sp_bwd_ev st with Hide-ev-elim msgBF (P-loop pStr0) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_Sp_bwd_tau : ∀ {S′} → (P-loop pStr0 ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (IS stStreaming))) ═[ τ ]═► W′ × RState W′ S′)
rs_Sp_bwd_tau st with P-loop-τ st
... | refl = _ , wτ (τ*-step (im-S-τ) τ*-refl) , rsV

rs_W6p_fwd_ev : (b : Block) → ∀ {l W′} → (JP (CB-loop stStreaming) (SB-blk b)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-blkD b ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W6p_fwd_ev b st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-loop stStreaming) (SB-blk b)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-loop stStreaming) (SB-blk b) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 (sVis () _) sstp
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis () _) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis () _)
...   | evL {e = apiBF recvBFBlock} ¬m2 (sVis () _)
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis () _)
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)

rs_W6p_fwd_tau : (b : Block) → ∀ {W′} → (JP (CB-loop stStreaming) (SB-blk b)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-blkD b ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W6p_fwd_tau b st with W6-τ st
... | refl = _ , wτ (τ*-step (sp-PblkD-τ b) τ*-refl) , (rsWp b)

rs_W6p_bwd_ev : (b : Block) → ∀ {l S′} → (P-blkD b ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (SB-blk b))) ═[ ev l ]═► W′ × RState W′ S′)
rs_W6p_bwd_ev b st with Hide-ev-elim msgBF (P-blkD b) st
... | heV {e = MsgBlock}                 P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_W6p_bwd_tau : (b : Block) → ∀ {S′} → (P-blkD b ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-loop stStreaming) (SB-blk b))) ═[ τ ]═► W′ × RState W′ S′)
rs_W6p_bwd_tau b st with P-blkD-τ st
... | refl = _ , wτ (τ*-step (im-W6-τ b) (τ*-step (im-W-τ b) τ*-refl)) , (rsW2 b)

rs_W4p_fwd_ev : (b b′ : Block) → ∀ {l W′} → (JP (CB-blk b) (SB-blk b′)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-blkP b b′ ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W4p_fwd_ev b b′ st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-blk b′)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (SB-blk b′) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
rs_W4p_fwd_ev b b′ st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = _ , wev (τ*-step (sp-PblkP-τ b b′) (τ*-step (sp-Ploop-τ (pStr2 b b′)) τ*-refl)) (sp-pStr2-recv b b′) τ*-refl , (rsW6′ b′)
rs_W4p_fwd_ev b b′ st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _

rs_W4p_fwd_tau : (b b′ : Block) → ∀ {W′} → (JP (CB-blk b) (SB-blk b′)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-blkP b b′ ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W4p_fwd_tau b b′ st = ⊥-elim (W4-noτ st)

rs_W4p_bwd_ev : (b b′ : Block) → ∀ {l S′} → (P-blkP b b′ ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (SB-blk b′))) ═[ ev l ]═► W′ × RState W′ S′)
rs_W4p_bwd_ev b b′ st with Hide-ev-elim msgBF (P-blkP b b′) st
... | heV {e = MsgBlock}                 P' ¬m stp = ⊥-elim (¬m Poly.tt)
... | heV {e = MsgRequestRange}          P' ¬m (sVis {at = (_ , MsgRequestRange)} refl ())
... | heV {e = MsgStartBatch}            P' ¬m (sVis {at = (_ , MsgStartBatch)}   refl ())
... | heV {e = MsgNoBlocks}              P' ¬m (sVis {at = (_ , MsgNoBlocks)}     refl ())
... | heV {e = MsgBatchDone}             P' ¬m (sVis {at = (_ , MsgBatchDone)}    refl ())
... | heV {e = MsgClientDone}            P' ¬m (sVis {at = (_ , MsgClientDone)}   refl ())
... | heV {e = apiBF m}                  P' ¬m (sVis {at = (_ , apiBF m)}         refl ())
... | he√ ()

rs_W4p_bwd_tau : (b b′ : Block) → ∀ {S′} → (P-blkP b b′ ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (SB-blk b′))) ═[ τ ]═► W′ × RState W′ S′)
rs_W4p_bwd_tau b b′ st with P-blkP-τ st
... | refl = _ , wτ τ*-refl , (rsW4q b b′)

rs_W4q_fwd_ev : (b b′ : Block) → ∀ {l W′} → (JP (CB-blk b) (SB-blk b′)) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop (pStr2 b b′) ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W4q_fwd_ev b b′ st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-blk b′)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (SB-blk b′) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
rs_W4q_fwd_ev b b′ st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = _ , wev (τ*-step (sp-Ploop-τ (pStr2 b b′)) τ*-refl) (sp-pStr2-recv b b′) τ*-refl , (rsW6′ b′)
rs_W4q_fwd_ev b b′ st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _

rs_W4q_fwd_tau : (b b′ : Block) → ∀ {W′} → (JP (CB-blk b) (SB-blk b′)) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop (pStr2 b b′) ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W4q_fwd_tau b b′ st = ⊥-elim (W4-noτ st)

rs_W4q_bwd_ev : (b b′ : Block) → ∀ {l S′} → (P-loop (pStr2 b b′) ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (SB-blk b′))) ═[ ev l ]═► W′ × RState W′ S′)
rs_W4q_bwd_ev b b′ st with Hide-ev-elim msgBF (P-loop (pStr2 b b′)) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_W4q_bwd_tau : (b b′ : Block) → ∀ {S′} → (P-loop (pStr2 b b′) ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) (SB-blk b′))) ═[ τ ]═► W′ × RState W′ S′)
rs_W4q_bwd_tau b b′ st with P-loop-τ st
... | refl = _ , wτ τ*-refl , (rsW4 b b′)

rs_W5q_fwd_ev : (b : Block) → ∀ {l W′} → (JP (CB-blk b) SB-bdone) ─[ ev l ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop (pStrD b) ∖ msgBF)) ═[ ev l ]═► S′ × RState W′ S′)
rs_W5q_fwd_ev b st with Hide-ev-elim msgBF (AbsOps.Par msgBF mrg (CB-blk b) (SB-bdone)) st
... | he√ ()
... | heV P' ¬m pev with Par-ev-elim msgBF mrg (CB-blk b) (SB-bdone) pev
...   | evSync m2 cstp sstp = ⊥-elim (¬m m2)
...   | evBoth {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ()) sstp
...   | evBoth {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ()) sstp
...   | evBoth {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ()) sstp
...   | evBoth {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ()) sstp
...   | evBoth {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ()) sstp
...   | evBoth {e = apiBF recvBFBlock} ¬m2 cstp (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evBoth {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ()) sstp
...   | evBoth {e = MsgRequestRange} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgStartBatch} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgNoBlocks} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBlock} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgBatchDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evBoth {e = MsgClientDone} ¬m2 cstp sstp = ⊥-elim (¬m2 _)
...   | evL {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evL {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evL {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evL {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evL {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evL {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evL {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evL {e = MsgRequestRange} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgStartBatch} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgNoBlocks} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBlock} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgBatchDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evL {e = MsgClientDone} ¬m2 cstp = ⊥-elim (¬m2 _)
...   | evR {e = apiBF sendBFRequestRange} ¬m2 (sVis {at = (_ , apiBF sendBFRequestRange)} refl ())
...   | evR {e = apiBF sendBFClientDone} ¬m2 (sVis {at = (_ , apiBF sendBFClientDone)} refl ())
...   | evR {e = apiBF sendBFStartBatch} ¬m2 (sVis {at = (_ , apiBF sendBFStartBatch)} refl ())
...   | evR {e = apiBF sendBFNoBlocks} ¬m2 (sVis {at = (_ , apiBF sendBFNoBlocks)} refl ())
...   | evR {e = apiBF sendBFBlock} ¬m2 (sVis {at = (_ , apiBF sendBFBlock)} refl ())
...   | evR {e = apiBF sendBFBatchDone} ¬m2 (sVis {at = (_ , apiBF sendBFBatchDone)} refl ())
...   | evR {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} refl ())
...   | evR {e = apiBF reqBFRange} ¬m2 (sVis {at = (_ , apiBF reqBFRange)} refl ())
...   | evR {e = MsgRequestRange} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgStartBatch} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgNoBlocks} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBlock} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgBatchDone} ¬m2 sstp = ⊥-elim (¬m2 _)
...   | evR {e = MsgClientDone} ¬m2 sstp = ⊥-elim (¬m2 _)
rs_W5q_fwd_ev b st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl cbreq) with aa ≟ b
... | yes refl with cbreq
...   | refl = _ , wev (τ*-step (sp-Ploop-τ (pStrD b)) τ*-refl) (sp-pStrD-recv b) τ*-refl , rsW7
rs_W5q_fwd_ev b st | heV P' ¬m pev | evL {e = apiBF recvBFBlock} ¬m2 (sVis {at = (_ , apiBF recvBFBlock)} {a = aa} refl ()) | no _

rs_W5q_fwd_tau : (b : Block) → ∀ {W′} → (JP (CB-blk b) SB-bdone) ─[ τ ]─► W′ → Σ[ S′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((P-loop (pStrD b) ∖ msgBF)) ═[ τ ]═► S′ × RState W′ S′)
rs_W5q_fwd_tau b st = ⊥-elim (W5-noτ st)

rs_W5q_bwd_ev : (b : Block) → ∀ {l S′} → (P-loop (pStrD b) ∖ msgBF) ─[ ev l ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) SB-bdone)) ═[ ev l ]═► W′ × RState W′ S′)
rs_W5q_bwd_ev b st with Hide-ev-elim msgBF (P-loop (pStrD b)) st
... | heV P' ¬m (sVis () _)
... | he√ ()

rs_W5q_bwd_tau : (b : Block) → ∀ {S′} → (P-loop (pStrD b) ∖ msgBF) ─[ τ ]─► S′ → Σ[ W′ ∈ PTree BFAbsEv (ExtI BFAbsEv) Rr ] (((JP (CB-blk b) SB-bdone)) ═[ τ ]═► W′ × RState W′ S′)
rs_W5q_bwd_tau b st with P-loop-τ st
... | refl = _ , wτ τ*-refl , (rsW5 b)

-- the two guarded builders (mkDRˢ = swapped orientation).
mkDR  : ∀ {W S} → RState W S → DRbisim Rr W S
mkDRˢ : ∀ {W S} → RState W S → DRbisim Rr S W
mkDR rsA .fwd .on-ev  st = let q = rs_A_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsA .fwd .on-tau st = let q = rs_A_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsA .bwd .on-ev  st = let q = rs_A_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsA .bwd .on-tau st = let q = rs_A_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsA .div→ d = ⊥-elim (nd-A d)
mkDR rsA .div← d = ⊥-elim (specP-nd-IT pIdle d)
mkDR rsZ .fwd .on-ev  st = let q = rs_Z_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsZ .fwd .on-tau st = let q = rs_Z_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsZ .bwd .on-ev  st = let q = rs_Z_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsZ .bwd .on-tau st = let q = rs_Z_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsZ .div→ d = ⊥-elim (nd-Z d)
mkDR rsZ .div← d = ⊥-elim (specP-nd-IT pDone d)
mkDR (rsB r) .fwd .on-ev  st = let q = rs_B_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsB r) .fwd .on-tau st = let q = rs_B_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsB r) .bwd .on-ev  st = let q = rs_B_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsB r) .bwd .on-tau st = let q = rs_B_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsB r) .div→ d = ⊥-elim (nd-B d)
mkDR (rsB r) .div← d = ⊥-elim (specP-nd-req d)
mkDR (rsTa r) .fwd .on-ev  st = let q = rs_Ta_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsTa r) .fwd .on-tau st = let q = rs_Ta_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsTa r) .bwd .on-ev  st = let q = rs_Ta_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsTa r) .bwd .on-tau st = let q = rs_Ta_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsTa r) .div→ d = ⊥-elim (nd-Ta d)
mkDR (rsTa r) .div← d = ⊥-elim (specP-nd-req d)
mkDR (rsD r) .fwd .on-ev  st = let q = rs_D_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsD r) .fwd .on-tau st = let q = rs_D_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsD r) .bwd .on-ev  st = let q = rs_D_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsD r) .bwd .on-tau st = let q = rs_D_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsD r) .div→ d = ⊥-elim (nd-D d)
mkDR (rsD r) .div← d = ⊥-elim (specP-nd-req2 d)
mkDR (rsF r) .fwd .on-ev  st = let q = rs_F_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsF r) .fwd .on-tau st = let q = rs_F_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsF r) .bwd .on-ev  st = let q = rs_F_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsF r) .bwd .on-tau st = let q = rs_F_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsF r) .div→ d = ⊥-elim (nd-F d)
mkDR (rsF r) .div← d = ⊥-elim (specP-nd-req2 d)
mkDR rsC .fwd .on-ev  st = let q = rs_C_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsC .fwd .on-tau st = let q = rs_C_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsC .bwd .on-ev  st = let q = rs_C_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsC .bwd .on-tau st = let q = rs_C_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsC .div→ d = ⊥-elim (nd-C d)
mkDR rsC .div← d = ⊥-elim (specP-nd-cdone d)
mkDR rsTb .fwd .on-ev  st = let q = rs_Tb_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsTb .fwd .on-tau st = let q = rs_Tb_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsTb .bwd .on-ev  st = let q = rs_Tb_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsTb .bwd .on-tau st = let q = rs_Tb_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsTb .div→ d = ⊥-elim (nd-Tb d)
mkDR rsTb .div← d = ⊥-elim (specP-nd-cdone d)
mkDR rsE .fwd .on-ev  st = let q = rs_E_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsE .fwd .on-tau st = let q = rs_E_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsE .bwd .on-ev  st = let q = rs_E_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsE .bwd .on-tau st = let q = rs_E_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsE .div→ d = ⊥-elim (nd-E d)
mkDR rsE .div← d = ⊥-elim (specP-nd-loop pDone d)
mkDR rsE1 .fwd .on-ev  st = let q = rs_E1_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsE1 .fwd .on-tau st = let q = rs_E1_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsE1 .bwd .on-ev  st = let q = rs_E1_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsE1 .bwd .on-tau st = let q = rs_E1_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsE1 .div→ d = ⊥-elim (nd-E1 d)
mkDR rsE1 .div← d = ⊥-elim (specP-nd-loop pDone d)
mkDR rsE2 .fwd .on-ev  st = let q = rs_E2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsE2 .fwd .on-tau st = let q = rs_E2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsE2 .bwd .on-ev  st = let q = rs_E2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsE2 .bwd .on-tau st = let q = rs_E2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsE2 .div→ d = ⊥-elim (nd-E2 d)
mkDR rsE2 .div← d = ⊥-elim (specP-nd-loop pDone d)
mkDR rsG .fwd .on-ev  st = let q = rs_G_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG .fwd .on-tau st = let q = rs_G_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsG .bwd .on-ev  st = let q = rs_G_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG .bwd .on-tau st = let q = rs_G_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsG .div→ d = ⊥-elim (nd-G d)
mkDR rsG .div← d = ⊥-elim (specP-nd-IT pBusy d)
mkDR rsH .fwd .on-ev  st = let q = rs_H_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsH .fwd .on-tau st = let q = rs_H_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsH .bwd .on-ev  st = let q = rs_H_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsH .bwd .on-tau st = let q = rs_H_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsH .div→ d = ⊥-elim (nd-H d)
mkDR rsH .div← d = ⊥-elim (specP-nd-IT pBusy d)
mkDR rsI .fwd .on-ev  st = let q = rs_I_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsI .fwd .on-tau st = let q = rs_I_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsI .bwd .on-ev  st = let q = rs_I_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsI .bwd .on-tau st = let q = rs_I_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsI .div→ d = ⊥-elim (nd-I d)
mkDR rsI .div← d = ⊥-elim (specP-nd-IT pBusy d)
mkDR rsJ .fwd .on-ev  st = let q = rs_J_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsJ .fwd .on-tau st = let q = rs_J_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsJ .bwd .on-ev  st = let q = rs_J_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsJ .bwd .on-tau st = let q = rs_J_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsJ .div→ d = ⊥-elim (nd-J d)
mkDR rsJ .div← d = ⊥-elim (specP-nd-IT pBusy d)
mkDR rsK .fwd .on-ev  st = let q = rs_K_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsK .fwd .on-tau st = let q = rs_K_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsK .bwd .on-ev  st = let q = rs_K_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsK .bwd .on-tau st = let q = rs_K_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsK .div→ d = ⊥-elim (nd-K d)
mkDR rsK .div← d = ⊥-elim (specP-nd-sbatch d)
mkDR rsL .fwd .on-ev  st = let q = rs_L_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsL .fwd .on-tau st = let q = rs_L_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsL .bwd .on-ev  st = let q = rs_L_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsL .bwd .on-tau st = let q = rs_L_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsL .div→ d = ⊥-elim (nd-L d)
mkDR rsL .div← d = ⊥-elim (specP-nd-noblk d)
mkDR rsM .fwd .on-ev  st = let q = rs_M_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM .fwd .on-tau st = let q = rs_M_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsM .bwd .on-ev  st = let q = rs_M_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM .bwd .on-tau st = let q = rs_M_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsM .div→ d = ⊥-elim (nd-M d)
mkDR rsM .div← d = ⊥-elim (specP-nd-sbatch d)
mkDR rsN .fwd .on-ev  st = let q = rs_N_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN .fwd .on-tau st = let q = rs_N_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsN .bwd .on-ev  st = let q = rs_N_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN .bwd .on-tau st = let q = rs_N_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsN .div→ d = ⊥-elim (nd-N d)
mkDR rsN .div← d = ⊥-elim (specP-nd-noblk d)
mkDR rsP .fwd .on-ev  st = let q = rs_P_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsP .fwd .on-tau st = let q = rs_P_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsP .bwd .on-ev  st = let q = rs_P_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsP .bwd .on-tau st = let q = rs_P_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsP .div→ d = ⊥-elim (nd-P d)
mkDR rsP .div← d = ⊥-elim (specP-nd-loop pStr0 d)
mkDR rsQ .fwd .on-ev  st = let q = rs_Q_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsQ .fwd .on-tau st = let q = rs_Q_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsQ .bwd .on-ev  st = let q = rs_Q_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsQ .bwd .on-tau st = let q = rs_Q_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsQ .div→ d = ⊥-elim (nd-Q d)
mkDR rsQ .div← d = ⊥-elim (specP-nd-loop pIdle d)
mkDR rsR .fwd .on-ev  st = let q = rs_R_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsR .fwd .on-tau st = let q = rs_R_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsR .bwd .on-ev  st = let q = rs_R_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsR .bwd .on-tau st = let q = rs_R_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsR .div→ d = ⊥-elim (nd-R d)
mkDR rsR .div← d = ⊥-elim (specP-nd-IT pStr0 d)
mkDR rsS .fwd .on-ev  st = let q = rs_S_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsS .fwd .on-tau st = let q = rs_S_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsS .bwd .on-ev  st = let q = rs_S_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsS .bwd .on-tau st = let q = rs_S_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsS .div→ d = ⊥-elim (nd-S d)
mkDR rsS .div← d = ⊥-elim (specP-nd-IT pStr0 d)
mkDR rsT .fwd .on-ev  st = let q = rs_T_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsT .fwd .on-tau st = let q = rs_T_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsT .bwd .on-ev  st = let q = rs_T_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsT .bwd .on-tau st = let q = rs_T_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsT .div→ d = ⊥-elim (nd-T d)
mkDR rsT .div← d = ⊥-elim (specP-nd-IT pIdle d)
mkDR rsU .fwd .on-ev  st = let q = rs_U_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsU .fwd .on-tau st = let q = rs_U_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsU .bwd .on-ev  st = let q = rs_U_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsU .bwd .on-tau st = let q = rs_U_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsU .div→ d = ⊥-elim (nd-U d)
mkDR rsU .div← d = ⊥-elim (specP-nd-loop pIdle d)
mkDR rsV .fwd .on-ev  st = let q = rs_V_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsV .fwd .on-tau st = let q = rs_V_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsV .bwd .on-ev  st = let q = rs_V_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsV .bwd .on-tau st = let q = rs_V_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsV .div→ d = ⊥-elim (nd-V d)
mkDR rsV .div← d = ⊥-elim (specP-nd-IT pStr0 d)
mkDR (rsW b) .fwd .on-ev  st = let q = rs_W_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW b) .fwd .on-tau st = let q = rs_W_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW b) .bwd .on-ev  st = let q = rs_W_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW b) .bwd .on-tau st = let q = rs_W_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW b) .div→ d = ⊥-elim (nd-W d)
mkDR (rsW b) .div← d = ⊥-elim (specP-nd-blk0 d)
mkDR (rsW2 b) .fwd .on-ev  st = let q = rs_W2_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2 b) .fwd .on-tau st = let q = rs_W2_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW2 b) .bwd .on-ev  st = let q = rs_W2_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2 b) .bwd .on-tau st = let q = rs_W2_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW2 b) .div→ d = ⊥-elim (nd-W2 d)
mkDR (rsW2 b) .div← d = ⊥-elim (specP-nd-loop (pStr1 b) d)
mkDR (rsW3 b) .fwd .on-ev  st = let q = rs_W3_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3 b) .fwd .on-tau st = let q = rs_W3_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW3 b) .bwd .on-ev  st = let q = rs_W3_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3 b) .bwd .on-tau st = let q = rs_W3_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW3 b) .div→ d = ⊥-elim (nd-W3 d)
mkDR (rsW3 b) .div← d = ⊥-elim (specP-nd-IT (pStr1 b) d)
mkDR (rsW4 b b′) .fwd .on-ev  st = let q = rs_W4_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4 b b′) .fwd .on-tau st = let q = rs_W4_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4 b b′) .bwd .on-ev  st = let q = rs_W4_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4 b b′) .bwd .on-tau st = let q = rs_W4_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4 b b′) .div→ d = ⊥-elim (nd-W4 d)
mkDR (rsW4 b b′) .div← d = ⊥-elim (specP-nd-IT (pStr2 b b′) d)
mkDR (rsW5 b) .fwd .on-ev  st = let q = rs_W5_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW5 b) .fwd .on-tau st = let q = rs_W5_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW5 b) .bwd .on-ev  st = let q = rs_W5_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW5 b) .bwd .on-tau st = let q = rs_W5_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW5 b) .div→ d = ⊥-elim (nd-W5 d)
mkDR (rsW5 b) .div← d = ⊥-elim (specP-nd-IT (pStrD b) d)
mkDR (rsW6 b) .fwd .on-ev  st = let q = rs_W6_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW6 b) .fwd .on-tau st = let q = rs_W6_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW6 b) .bwd .on-ev  st = let q = rs_W6_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW6 b) .bwd .on-tau st = let q = rs_W6_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW6 b) .div→ d = ⊥-elim (nd-W6 d)
mkDR (rsW6 b) .div← d = ⊥-elim (specP-nd-blk0 d)
mkDR rsW7 .fwd .on-ev  st = let q = rs_W7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsW7 .fwd .on-tau st = let q = rs_W7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsW7 .bwd .on-ev  st = let q = rs_W7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsW7 .bwd .on-tau st = let q = rs_W7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsW7 .div→ d = ⊥-elim (nd-W7 d)
mkDR rsW7 .div← d = ⊥-elim (specP-nd-bdone d)
mkDR rsY .fwd .on-ev  st = let q = rs_Y_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsY .fwd .on-tau st = let q = rs_Y_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsY .bwd .on-ev  st = let q = rs_Y_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsY .bwd .on-tau st = let q = rs_Y_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsY .div→ d = ⊥-elim (nd-Y d)
mkDR rsY .div← d = ⊥-elim (specP-nd-bdone d)
mkDR rsGp .fwd .on-ev  st = let q = rs_Gp_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsGp .fwd .on-tau st = let q = rs_Gp_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsGp .bwd .on-ev  st = let q = rs_Gp_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsGp .bwd .on-tau st = let q = rs_Gp_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsGp .div→ d = ⊥-elim (nd-G d)
mkDR rsGp .div← d = ⊥-elim (specP-nd-loop pBusy d)
mkDR rsHp .fwd .on-ev  st = let q = rs_Hp_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsHp .fwd .on-tau st = let q = rs_Hp_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsHp .bwd .on-ev  st = let q = rs_Hp_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsHp .bwd .on-tau st = let q = rs_Hp_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsHp .div→ d = ⊥-elim (nd-H d)
mkDR rsHp .div← d = ⊥-elim (specP-nd-loop pBusy d)
mkDR (rsWp b) .fwd .on-ev  st = let q = rs_Wp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWp b) .fwd .on-tau st = let q = rs_Wp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsWp b) .bwd .on-ev  st = let q = rs_Wp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWp b) .bwd .on-tau st = let q = rs_Wp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsWp b) .div→ d = ⊥-elim (nd-W d)
mkDR (rsWp b) .div← d = ⊥-elim (specP-nd-loop (pStr1 b) d)
mkDR rsS′ .fwd .on-ev  st = let q = rs_Sp_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsS′ .fwd .on-tau st = let q = rs_Sp_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsS′ .bwd .on-ev  st = let q = rs_Sp_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsS′ .bwd .on-tau st = let q = rs_Sp_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsS′ .div→ d = ⊥-elim (nd-S d)
mkDR rsS′ .div← d = ⊥-elim (specP-nd-loop pStr0 d)
mkDR (rsW6′ b) .fwd .on-ev  st = let q = rs_W6p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW6′ b) .fwd .on-tau st = let q = rs_W6p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW6′ b) .bwd .on-ev  st = let q = rs_W6p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW6′ b) .bwd .on-tau st = let q = rs_W6p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW6′ b) .div→ d = ⊥-elim (nd-W6 d)
mkDR (rsW6′ b) .div← d = ⊥-elim (specP-nd-blkD d)
mkDR (rsW4p b b′) .fwd .on-ev  st = let q = rs_W4p_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4p b b′) .fwd .on-tau st = let q = rs_W4p_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4p b b′) .bwd .on-ev  st = let q = rs_W4p_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4p b b′) .bwd .on-tau st = let q = rs_W4p_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4p b b′) .div→ d = ⊥-elim (nd-W4 d)
mkDR (rsW4p b b′) .div← d = ⊥-elim (specP-nd-blkP d)
mkDR (rsW4q b b′) .fwd .on-ev  st = let q = rs_W4q_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4q b b′) .fwd .on-tau st = let q = rs_W4q_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW4q b b′) .bwd .on-ev  st = let q = rs_W4q_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4q b b′) .bwd .on-tau st = let q = rs_W4q_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW4q b b′) .div→ d = ⊥-elim (nd-W4 d)
mkDR (rsW4q b b′) .div← d = ⊥-elim (specP-nd-loop (pStr2 b b′) d)
mkDR (rsW5q b) .fwd .on-ev  st = let q = rs_W5q_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW5q b) .fwd .on-tau st = let q = rs_W5q_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR (rsW5q b) .bwd .on-ev  st = let q = rs_W5q_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW5q b) .bwd .on-tau st = let q = rs_W5q_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR (rsW5q b) .div→ d = ⊥-elim (nd-W5 d)
mkDR (rsW5q b) .div← d = ⊥-elim (specP-nd-loop (pStrD b) d)
mkDR rsDL .fwd .on-ev  st = let q = rs_DL_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsDL .fwd .on-tau st = let q = rs_DL_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDR rsDL .bwd .on-ev  st = let q = rs_DL_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsDL .bwd .on-tau st = let q = rs_DL_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDR rsDL .div→ d = d
mkDR rsDL .div← d = d
mkDRˢ rsA .fwd .on-ev  st = let q = rs_A_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsA .fwd .on-tau st = let q = rs_A_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsA .bwd .on-ev  st = let q = rs_A_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsA .bwd .on-tau st = let q = rs_A_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsA .div→ d = ⊥-elim (specP-nd-IT pIdle d)
mkDRˢ rsA .div← d = ⊥-elim (nd-A d)
mkDRˢ rsZ .fwd .on-ev  st = let q = rs_Z_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsZ .fwd .on-tau st = let q = rs_Z_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsZ .bwd .on-ev  st = let q = rs_Z_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsZ .bwd .on-tau st = let q = rs_Z_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsZ .div→ d = ⊥-elim (specP-nd-IT pDone d)
mkDRˢ rsZ .div← d = ⊥-elim (nd-Z d)
mkDRˢ (rsB r) .fwd .on-ev  st = let q = rs_B_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsB r) .fwd .on-tau st = let q = rs_B_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsB r) .bwd .on-ev  st = let q = rs_B_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsB r) .bwd .on-tau st = let q = rs_B_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsB r) .div→ d = ⊥-elim (specP-nd-req d)
mkDRˢ (rsB r) .div← d = ⊥-elim (nd-B d)
mkDRˢ (rsTa r) .fwd .on-ev  st = let q = rs_Ta_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsTa r) .fwd .on-tau st = let q = rs_Ta_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsTa r) .bwd .on-ev  st = let q = rs_Ta_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsTa r) .bwd .on-tau st = let q = rs_Ta_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsTa r) .div→ d = ⊥-elim (specP-nd-req d)
mkDRˢ (rsTa r) .div← d = ⊥-elim (nd-Ta d)
mkDRˢ (rsD r) .fwd .on-ev  st = let q = rs_D_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsD r) .fwd .on-tau st = let q = rs_D_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsD r) .bwd .on-ev  st = let q = rs_D_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsD r) .bwd .on-tau st = let q = rs_D_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsD r) .div→ d = ⊥-elim (specP-nd-req2 d)
mkDRˢ (rsD r) .div← d = ⊥-elim (nd-D d)
mkDRˢ (rsF r) .fwd .on-ev  st = let q = rs_F_bwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsF r) .fwd .on-tau st = let q = rs_F_bwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsF r) .bwd .on-ev  st = let q = rs_F_fwd_ev r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsF r) .bwd .on-tau st = let q = rs_F_fwd_tau r st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsF r) .div→ d = ⊥-elim (specP-nd-req2 d)
mkDRˢ (rsF r) .div← d = ⊥-elim (nd-F d)
mkDRˢ rsC .fwd .on-ev  st = let q = rs_C_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsC .fwd .on-tau st = let q = rs_C_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsC .bwd .on-ev  st = let q = rs_C_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsC .bwd .on-tau st = let q = rs_C_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsC .div→ d = ⊥-elim (specP-nd-cdone d)
mkDRˢ rsC .div← d = ⊥-elim (nd-C d)
mkDRˢ rsTb .fwd .on-ev  st = let q = rs_Tb_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsTb .fwd .on-tau st = let q = rs_Tb_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsTb .bwd .on-ev  st = let q = rs_Tb_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsTb .bwd .on-tau st = let q = rs_Tb_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsTb .div→ d = ⊥-elim (specP-nd-cdone d)
mkDRˢ rsTb .div← d = ⊥-elim (nd-Tb d)
mkDRˢ rsE .fwd .on-ev  st = let q = rs_E_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsE .fwd .on-tau st = let q = rs_E_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsE .bwd .on-ev  st = let q = rs_E_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsE .bwd .on-tau st = let q = rs_E_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsE .div→ d = ⊥-elim (specP-nd-loop pDone d)
mkDRˢ rsE .div← d = ⊥-elim (nd-E d)
mkDRˢ rsE1 .fwd .on-ev  st = let q = rs_E1_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsE1 .fwd .on-tau st = let q = rs_E1_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsE1 .bwd .on-ev  st = let q = rs_E1_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsE1 .bwd .on-tau st = let q = rs_E1_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsE1 .div→ d = ⊥-elim (specP-nd-loop pDone d)
mkDRˢ rsE1 .div← d = ⊥-elim (nd-E1 d)
mkDRˢ rsE2 .fwd .on-ev  st = let q = rs_E2_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsE2 .fwd .on-tau st = let q = rs_E2_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsE2 .bwd .on-ev  st = let q = rs_E2_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsE2 .bwd .on-tau st = let q = rs_E2_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsE2 .div→ d = ⊥-elim (specP-nd-loop pDone d)
mkDRˢ rsE2 .div← d = ⊥-elim (nd-E2 d)
mkDRˢ rsG .fwd .on-ev  st = let q = rs_G_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG .fwd .on-tau st = let q = rs_G_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsG .bwd .on-ev  st = let q = rs_G_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG .bwd .on-tau st = let q = rs_G_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsG .div→ d = ⊥-elim (specP-nd-IT pBusy d)
mkDRˢ rsG .div← d = ⊥-elim (nd-G d)
mkDRˢ rsH .fwd .on-ev  st = let q = rs_H_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsH .fwd .on-tau st = let q = rs_H_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsH .bwd .on-ev  st = let q = rs_H_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsH .bwd .on-tau st = let q = rs_H_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsH .div→ d = ⊥-elim (specP-nd-IT pBusy d)
mkDRˢ rsH .div← d = ⊥-elim (nd-H d)
mkDRˢ rsI .fwd .on-ev  st = let q = rs_I_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsI .fwd .on-tau st = let q = rs_I_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsI .bwd .on-ev  st = let q = rs_I_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsI .bwd .on-tau st = let q = rs_I_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsI .div→ d = ⊥-elim (specP-nd-IT pBusy d)
mkDRˢ rsI .div← d = ⊥-elim (nd-I d)
mkDRˢ rsJ .fwd .on-ev  st = let q = rs_J_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsJ .fwd .on-tau st = let q = rs_J_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsJ .bwd .on-ev  st = let q = rs_J_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsJ .bwd .on-tau st = let q = rs_J_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsJ .div→ d = ⊥-elim (specP-nd-IT pBusy d)
mkDRˢ rsJ .div← d = ⊥-elim (nd-J d)
mkDRˢ rsK .fwd .on-ev  st = let q = rs_K_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsK .fwd .on-tau st = let q = rs_K_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsK .bwd .on-ev  st = let q = rs_K_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsK .bwd .on-tau st = let q = rs_K_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsK .div→ d = ⊥-elim (specP-nd-sbatch d)
mkDRˢ rsK .div← d = ⊥-elim (nd-K d)
mkDRˢ rsL .fwd .on-ev  st = let q = rs_L_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsL .fwd .on-tau st = let q = rs_L_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsL .bwd .on-ev  st = let q = rs_L_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsL .bwd .on-tau st = let q = rs_L_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsL .div→ d = ⊥-elim (specP-nd-noblk d)
mkDRˢ rsL .div← d = ⊥-elim (nd-L d)
mkDRˢ rsM .fwd .on-ev  st = let q = rs_M_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM .fwd .on-tau st = let q = rs_M_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsM .bwd .on-ev  st = let q = rs_M_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM .bwd .on-tau st = let q = rs_M_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsM .div→ d = ⊥-elim (specP-nd-sbatch d)
mkDRˢ rsM .div← d = ⊥-elim (nd-M d)
mkDRˢ rsN .fwd .on-ev  st = let q = rs_N_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN .fwd .on-tau st = let q = rs_N_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsN .bwd .on-ev  st = let q = rs_N_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN .bwd .on-tau st = let q = rs_N_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsN .div→ d = ⊥-elim (specP-nd-noblk d)
mkDRˢ rsN .div← d = ⊥-elim (nd-N d)
mkDRˢ rsP .fwd .on-ev  st = let q = rs_P_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsP .fwd .on-tau st = let q = rs_P_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsP .bwd .on-ev  st = let q = rs_P_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsP .bwd .on-tau st = let q = rs_P_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsP .div→ d = ⊥-elim (specP-nd-loop pStr0 d)
mkDRˢ rsP .div← d = ⊥-elim (nd-P d)
mkDRˢ rsQ .fwd .on-ev  st = let q = rs_Q_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsQ .fwd .on-tau st = let q = rs_Q_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsQ .bwd .on-ev  st = let q = rs_Q_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsQ .bwd .on-tau st = let q = rs_Q_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsQ .div→ d = ⊥-elim (specP-nd-loop pIdle d)
mkDRˢ rsQ .div← d = ⊥-elim (nd-Q d)
mkDRˢ rsR .fwd .on-ev  st = let q = rs_R_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsR .fwd .on-tau st = let q = rs_R_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsR .bwd .on-ev  st = let q = rs_R_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsR .bwd .on-tau st = let q = rs_R_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsR .div→ d = ⊥-elim (specP-nd-IT pStr0 d)
mkDRˢ rsR .div← d = ⊥-elim (nd-R d)
mkDRˢ rsS .fwd .on-ev  st = let q = rs_S_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsS .fwd .on-tau st = let q = rs_S_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsS .bwd .on-ev  st = let q = rs_S_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsS .bwd .on-tau st = let q = rs_S_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsS .div→ d = ⊥-elim (specP-nd-IT pStr0 d)
mkDRˢ rsS .div← d = ⊥-elim (nd-S d)
mkDRˢ rsT .fwd .on-ev  st = let q = rs_T_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsT .fwd .on-tau st = let q = rs_T_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsT .bwd .on-ev  st = let q = rs_T_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsT .bwd .on-tau st = let q = rs_T_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsT .div→ d = ⊥-elim (specP-nd-IT pIdle d)
mkDRˢ rsT .div← d = ⊥-elim (nd-T d)
mkDRˢ rsU .fwd .on-ev  st = let q = rs_U_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsU .fwd .on-tau st = let q = rs_U_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsU .bwd .on-ev  st = let q = rs_U_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsU .bwd .on-tau st = let q = rs_U_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsU .div→ d = ⊥-elim (specP-nd-loop pIdle d)
mkDRˢ rsU .div← d = ⊥-elim (nd-U d)
mkDRˢ rsV .fwd .on-ev  st = let q = rs_V_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsV .fwd .on-tau st = let q = rs_V_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsV .bwd .on-ev  st = let q = rs_V_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsV .bwd .on-tau st = let q = rs_V_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsV .div→ d = ⊥-elim (specP-nd-IT pStr0 d)
mkDRˢ rsV .div← d = ⊥-elim (nd-V d)
mkDRˢ (rsW b) .fwd .on-ev  st = let q = rs_W_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW b) .fwd .on-tau st = let q = rs_W_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW b) .bwd .on-ev  st = let q = rs_W_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW b) .bwd .on-tau st = let q = rs_W_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW b) .div→ d = ⊥-elim (specP-nd-blk0 d)
mkDRˢ (rsW b) .div← d = ⊥-elim (nd-W d)
mkDRˢ (rsW2 b) .fwd .on-ev  st = let q = rs_W2_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2 b) .fwd .on-tau st = let q = rs_W2_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW2 b) .bwd .on-ev  st = let q = rs_W2_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2 b) .bwd .on-tau st = let q = rs_W2_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW2 b) .div→ d = ⊥-elim (specP-nd-loop (pStr1 b) d)
mkDRˢ (rsW2 b) .div← d = ⊥-elim (nd-W2 d)
mkDRˢ (rsW3 b) .fwd .on-ev  st = let q = rs_W3_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3 b) .fwd .on-tau st = let q = rs_W3_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW3 b) .bwd .on-ev  st = let q = rs_W3_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3 b) .bwd .on-tau st = let q = rs_W3_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW3 b) .div→ d = ⊥-elim (specP-nd-IT (pStr1 b) d)
mkDRˢ (rsW3 b) .div← d = ⊥-elim (nd-W3 d)
mkDRˢ (rsW4 b b′) .fwd .on-ev  st = let q = rs_W4_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4 b b′) .fwd .on-tau st = let q = rs_W4_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4 b b′) .bwd .on-ev  st = let q = rs_W4_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4 b b′) .bwd .on-tau st = let q = rs_W4_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4 b b′) .div→ d = ⊥-elim (specP-nd-IT (pStr2 b b′) d)
mkDRˢ (rsW4 b b′) .div← d = ⊥-elim (nd-W4 d)
mkDRˢ (rsW5 b) .fwd .on-ev  st = let q = rs_W5_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW5 b) .fwd .on-tau st = let q = rs_W5_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW5 b) .bwd .on-ev  st = let q = rs_W5_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW5 b) .bwd .on-tau st = let q = rs_W5_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW5 b) .div→ d = ⊥-elim (specP-nd-IT (pStrD b) d)
mkDRˢ (rsW5 b) .div← d = ⊥-elim (nd-W5 d)
mkDRˢ (rsW6 b) .fwd .on-ev  st = let q = rs_W6_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW6 b) .fwd .on-tau st = let q = rs_W6_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW6 b) .bwd .on-ev  st = let q = rs_W6_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW6 b) .bwd .on-tau st = let q = rs_W6_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW6 b) .div→ d = ⊥-elim (specP-nd-blk0 d)
mkDRˢ (rsW6 b) .div← d = ⊥-elim (nd-W6 d)
mkDRˢ rsW7 .fwd .on-ev  st = let q = rs_W7_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsW7 .fwd .on-tau st = let q = rs_W7_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsW7 .bwd .on-ev  st = let q = rs_W7_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsW7 .bwd .on-tau st = let q = rs_W7_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsW7 .div→ d = ⊥-elim (specP-nd-bdone d)
mkDRˢ rsW7 .div← d = ⊥-elim (nd-W7 d)
mkDRˢ rsY .fwd .on-ev  st = let q = rs_Y_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsY .fwd .on-tau st = let q = rs_Y_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsY .bwd .on-ev  st = let q = rs_Y_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsY .bwd .on-tau st = let q = rs_Y_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsY .div→ d = ⊥-elim (specP-nd-bdone d)
mkDRˢ rsY .div← d = ⊥-elim (nd-Y d)
mkDRˢ rsGp .fwd .on-ev  st = let q = rs_Gp_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsGp .fwd .on-tau st = let q = rs_Gp_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsGp .bwd .on-ev  st = let q = rs_Gp_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsGp .bwd .on-tau st = let q = rs_Gp_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsGp .div→ d = ⊥-elim (specP-nd-loop pBusy d)
mkDRˢ rsGp .div← d = ⊥-elim (nd-G d)
mkDRˢ rsHp .fwd .on-ev  st = let q = rs_Hp_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsHp .fwd .on-tau st = let q = rs_Hp_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsHp .bwd .on-ev  st = let q = rs_Hp_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsHp .bwd .on-tau st = let q = rs_Hp_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsHp .div→ d = ⊥-elim (specP-nd-loop pBusy d)
mkDRˢ rsHp .div← d = ⊥-elim (nd-H d)
mkDRˢ (rsWp b) .fwd .on-ev  st = let q = rs_Wp_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWp b) .fwd .on-tau st = let q = rs_Wp_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsWp b) .bwd .on-ev  st = let q = rs_Wp_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWp b) .bwd .on-tau st = let q = rs_Wp_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsWp b) .div→ d = ⊥-elim (specP-nd-loop (pStr1 b) d)
mkDRˢ (rsWp b) .div← d = ⊥-elim (nd-W d)
mkDRˢ rsS′ .fwd .on-ev  st = let q = rs_Sp_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsS′ .fwd .on-tau st = let q = rs_Sp_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsS′ .bwd .on-ev  st = let q = rs_Sp_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsS′ .bwd .on-tau st = let q = rs_Sp_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsS′ .div→ d = ⊥-elim (specP-nd-loop pStr0 d)
mkDRˢ rsS′ .div← d = ⊥-elim (nd-S d)
mkDRˢ (rsW6′ b) .fwd .on-ev  st = let q = rs_W6p_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW6′ b) .fwd .on-tau st = let q = rs_W6p_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW6′ b) .bwd .on-ev  st = let q = rs_W6p_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW6′ b) .bwd .on-tau st = let q = rs_W6p_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW6′ b) .div→ d = ⊥-elim (specP-nd-blkD d)
mkDRˢ (rsW6′ b) .div← d = ⊥-elim (nd-W6 d)
mkDRˢ (rsW4p b b′) .fwd .on-ev  st = let q = rs_W4p_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4p b b′) .fwd .on-tau st = let q = rs_W4p_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4p b b′) .bwd .on-ev  st = let q = rs_W4p_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4p b b′) .bwd .on-tau st = let q = rs_W4p_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4p b b′) .div→ d = ⊥-elim (specP-nd-blkP d)
mkDRˢ (rsW4p b b′) .div← d = ⊥-elim (nd-W4 d)
mkDRˢ (rsW4q b b′) .fwd .on-ev  st = let q = rs_W4q_bwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4q b b′) .fwd .on-tau st = let q = rs_W4q_bwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW4q b b′) .bwd .on-ev  st = let q = rs_W4q_fwd_ev b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4q b b′) .bwd .on-tau st = let q = rs_W4q_fwd_tau b b′ st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW4q b b′) .div→ d = ⊥-elim (specP-nd-loop (pStr2 b b′) d)
mkDRˢ (rsW4q b b′) .div← d = ⊥-elim (nd-W4 d)
mkDRˢ (rsW5q b) .fwd .on-ev  st = let q = rs_W5q_bwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW5q b) .fwd .on-tau st = let q = rs_W5q_bwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ (rsW5q b) .bwd .on-ev  st = let q = rs_W5q_fwd_ev b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW5q b) .bwd .on-tau st = let q = rs_W5q_fwd_tau b st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ (rsW5q b) .div→ d = ⊥-elim (specP-nd-loop (pStrD b) d)
mkDRˢ (rsW5q b) .div← d = ⊥-elim (nd-W5 d)
mkDRˢ rsDL .fwd .on-ev  st = let q = rs_DL_bwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsDL .fwd .on-tau st = let q = rs_DL_bwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDRˢ (proj₂ (proj₂ q))
mkDRˢ rsDL .bwd .on-ev  st = let q = rs_DL_fwd_ev st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsDL .bwd .on-tau st = let q = rs_DL_fwd_tau st in proj₁ q , proj₁ (proj₂ q) , mkDR  (proj₂ (proj₂ q))
mkDRˢ rsDL .div→ d = d
mkDRˢ rsDL .div← d = d

------------------------------------------------------------------------
-- THE THEOREM: clientServerBF ∖ msgBF ≈DR BFabstractP ∖ msgBF.
------------------------------------------------------------------------
cs≈DR : (clientServerBF ∖ msgBF) ≈DR (BFabstractP ∖ msgBF)
cs≈DR = mkDR rsA

------------------------------------------------------------------------
-- COROLLARY: BFabstractP ∖ msgBF ⊑FD clientServerBF ∖ msgBF.
-- (The pipelined spec refines the distributed impl in the FD model.)
------------------------------------------------------------------------
-- the distributed impl refines the pipelined spec in the failures-divergences model
BFabsP-⊑FD : (BFabstractP ∖ msgBF) ⊑FD (clientServerBF ∖ msgBF)
BFabsP-⊑FD = proj₂ (drbisim→≈FD cs≈DR)
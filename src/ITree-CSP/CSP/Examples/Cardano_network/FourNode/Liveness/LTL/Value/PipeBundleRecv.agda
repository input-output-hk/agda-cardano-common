{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the BUNDLE-level receive-coupling SOURCE-PHASE
-- witness (`Praos.PipeBundleRecv`).
--
-- `PipeEvDriver.pres-relay`/`pres-cons` isolate the two `recvBFBlock`
-- receive-boundary crossings behind the guarded hypotheses `wUp`/`wDn` :
-- "the receiving driver's local BF CLIENT peer HELD the block
-- (`BFcHasBlk`) at the moment it fired `recvBFBlock`".  `PipeRecvSource`
-- discharged the NODE-LOCAL half — a `recvBFBlock` fire out of an ISOLATED
-- BF client `absBFc l cl bfc` forces `BFcHasBlk bfc`.  But the api cone
-- exposes the fire at the BUNDLE level (`absBundleG l cl sv …`), not at the
-- isolated client — so `wUp`/`wDn` need the fire pushed THROUGH the 12-peer
-- `⦀`-nest down to the isolated BF client.
--
-- THIS module supplies that bridge.  `bundleBF-ev-forces` MIRRORS
-- `SysIoLink6.absBundleBF-ev-prod`'s 12-peer `Par-ev-elim` dispatch, but
-- instead of FOLDING the fired BF-peer step back into a bundle successor
-- (`finishBFc-ev-abs`/`finishBFs-ev-abs`, which DISCARD the isolated peer
-- transition), it hands the isolated BF-client / BF-server transition to two
-- caller-supplied callbacks — so the caller keeps the isolated transition.
-- `bundle-recvBFBlock-forces-src` instantiates it with the `recvBFBlock`
-- event: the client callback is `PipeRecvSource.recvBFBlock-forces-src` (⇒
-- `BFcHasBlk bfc`), the server callback is `recvBFBlock-server-absurd` (a BF
-- server NEVER offers `recvBFBlock` — its abstract table `Tbfs` gives
-- `nxt … recvBFBlock ≡ nothing` at every server phase, refuted exactly as the
-- client witness does).  Event forms match definitionally
-- (`ιBF (apiBFev l d m) = apiBF l d m`).
--
-- LIGHT (a single 12-peer dispatch + a 14-phase server-table refutation;
-- imports only the R2 abstract bundle inversion machinery + `PipeRecvSource`
-- + `PipeInv.BFcHasBlk`).  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong; trans; sym; _≢_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleRecv (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

-- the operators used to shape a node (`⦀` interleave, `∅ES` empty sync set)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _⦀_ ) renaming ( ∅ES to ∅ESa )

import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA using
  ( CScPos; CSsPos; BFcPos; BFsPos; InertPos; kac; kas; tsc; tss; lnc; lns; lfc; lfs
  ; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil )
open SStep using
  ( NetProc; absBundleG; absKAc; absKAs; absCSc; absCSs; absBFc; absBFs
  ; absTSc; absTSs; absLNc; absLNs; absLFc; absLFs; coarsenBFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA using
  ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink5 blkA using ( Tbfs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA using
  ( bfEvDir
  ; absKAc-noBF; absKAs-noBF; absCSc-noBF; absCSs-noBF; absTSc-noBF; absTSs-noBF
  ; absLNc-noBF; absLNs-noBF; absLFc-noBF; absLFs-noBF
  ; absBFs-dir-noBoth; absBFc-dir-noBoth )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA using ( absBFc-ev-dir )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeRecvSource blkA using
  ( recvBFBlock-forces-src )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using ( BFcHasBlk )

------------------------------------------------------------------------
-- A BF SERVER never offers `recvBFBlock` (a client-received event): its
-- abstract table `Tbfs` gives `nxt … recvBFBlock ≡ nothing` at EVERY server
-- phase — refuted by the SAME `nothing-absurd` inversion as the client
-- witness (`PipeRecvSource.recvBFBlock-forces-src`), over all 14 `BFsPos`.
------------------------------------------------------------------------

-- firing `apiBFev … recvBFBlock` out of a BF server is impossible
recvBFBlock-server-absurd :
    (l : Link) (sv : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {a : _} {M : NetProc}
  → absBFs l sv bfs ─[ ev (evl (evLabel _ (ιBF (BF.apiBFev l′ d′ recvBFBlock)) a)) ]─► M
  → ⊥
recvBFBlock-server-absurd l sv (bsHead BF.stIdle) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv (bsHead BF.stBusy) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv (bsHead BF.stStreaming) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv (bsHead BF.stDone) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv (bsReq1 r) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv bsDone1 step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs bsDone1) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv bsStart1 step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs bsStart1) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv bsNoBlk1 step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs bsNoBlk1) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv (bsBlk1 b) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv bsBatchDone1 step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs bsBatchDone1) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv (bsSil BF.stIdle) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsSil BF.stIdle)) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv (bsSil BF.stBusy) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv (bsSil BF.stStreaming) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq = nothing-absurd ceq
recvBFBlock-server-absurd l sv (bsSil BF.stDone) step
  with tableSpec-ev-inv (Tbfs l sv) (coarsenBFs (bsSil BF.stDone)) step
... | q′ , ceq , Meq = nothing-absurd ceq

------------------------------------------------------------------------
-- The GENERAL bundle BF-fire dispatcher.  Mirror of
-- `SysIoLink6.absBundleBF-ev-prod`'s 12-peer `Par-ev-elim` cascade, but
-- routing the isolated BF-client / BF-server transition to caller callbacks
-- (`kc`/`ks`) instead of folding them into a bundle successor.  Every
-- non-BF peer branch refutes exactly as the original (event is a BF event).
------------------------------------------------------------------------

-- push a bundle BF-fire down to the isolated BF-client / BF-server transition
bundleBF-ev-forces :
    (l : Link) (cl sv : Dir) → cl ≢ sv
  → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc} {R : Set}
  → (∀ {P′} → absBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′ → R)
  → (∀ {P′} → absBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′ → R)
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → R
bundleBF-ev-forces l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} kc ks step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM     = ⊥-elim (absKAc-noBF l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noBF l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM     = ⊥-elim (absKAs-noBF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noBF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM     = ⊥-elim (absCSc-noBF l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noBF l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM     = ⊥-elim (absCSs-noBF l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noBF l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = kc sM
...         | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-dir-noBoth l sv bfs e₁ (λ q → cl≢sv (trans (sym (absBFc-ev-dir l cl bfc sM)) q))) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁)))))) (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = ks sM
...           | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁))))) (_ , sTail))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM     = ⊥-elim (absTSc-noBF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noBF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM     = ⊥-elim (absTSs-noBF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noBF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM     = ⊥-elim (absLNc-noBF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noBF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM     = ⊥-elim (absLNs-noBF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noBF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM     = ⊥-elim (absLFc-noBF l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noBF l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (absLFs-noBF l sv (lfs ip) e₁ (_ , qs))

------------------------------------------------------------------------
-- The bridge (`wUp`/`wDn` feeder): a `recvBFBlock` fire out of the bundle
-- forces its BF-client source phase `bfc` to hold the block.
------------------------------------------------------------------------

-- firing `apiBFev … recvBFBlock` from `absBundleG … bfc …` forces
-- `BFcHasBlk bfc` (the client held the block); the server branch is absurd
bundle-recvBFBlock-forces-src :
    (l : Link) (cl sv : Dir) → cl ≢ sv
  → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {l′ : Link} {d′ : Dir} {a : _} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip
       ─[ ev (evl (evLabel _ (ιBF (BF.apiBFev l′ d′ recvBFBlock)) a)) ]─► Bd′
  → BFcHasBlk bfc
bundle-recvBFBlock-forces-src l cl sv cl≢sv csc css bfc bfs ip step =
  bundleBF-ev-forces l cl sv cl≢sv csc css bfc bfs ip
    (recvBFBlock-forces-src l cl bfc)
    (λ sM → ⊥-elim (recvBFBlock-server-absurd l sv bfs sM))
    step

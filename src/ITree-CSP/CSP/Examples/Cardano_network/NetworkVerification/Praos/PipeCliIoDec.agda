{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the ISOLATED BF-CLIENT io SUCCESSOR DECODE
-- (`Praos.PipeCliIoDec`), the decode half of sub-obligation (b) of the
-- `PipeInvProd.TauIoS` arm.
--
-- `PipeBundleEvo.BFcDecode` hard-wires the field `(BFcHasBlk bfc′ → ⊥)`, which
-- is UNSATISFIABLE on an io: a BF client legitimately ENTERS its holding
-- position on the wire read
--
--     bcStream --output l d N2N_BlockFetch ! (…, blockFetch (MsgBlock b))--> bcAblk b
--
-- (`NodeSpecs.bfCnxt`:544-546 — and that is the ONLY row of the client table
-- that reaches `bcAblk`, checked before building, per the session-28 mandate).
-- The correct io fact is therefore the DISJUNCTION
--
--     `BfcIoSucc bfc′ a  =  (BFcHasBlk bfc′ → ⊥)  ⊎  PlIsBlk a`
--
-- — either the successor does not hold a block, or the READ PAYLOAD was one.
-- That is exactly the form the `PipeInv.Coupled` client clause consumes: with
-- `PipeMedKey.medium-ev-out-key` the same io pins the leg's cell to `full a` at
-- the read key, so `PlIsBlk a` IS `CellHasBlk (cellUp l s)` and the OLD cell
-- clause hands back `ProdSent` / `RelayFwd` outright.
--
-- Note the DIRECTION bookkeeping this relies on and which the four-node diamond
-- satisfies: node A's AB bundle is `absBundleG linkAB lo hi` (server at `hi`)
-- and node B's is `absBundleG linkAB hi lo` (client at `hi`), so the writing
-- server and the reading client share the cell key `(linkAB, hi, BF)` — the
-- leg's own `cellUp`.  Likewise `(linkBD, hi, BF)` for `cellDn`.
--
-- Bodies mirror `SysIoLink5.bfc-hstep` / `decBFc-ev-prod-abs` VERBATIM on the
-- io slice, reusing the frozen `bfc-fire-*` firing lemmas, `mkMbfc`, `Tbfc`,
-- `tableSpec-ev-inv` and `decBFc-sil-step`; the ONLY addition is the named
-- successor's block classification.
--
-- Imported by nothing yet.  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Maybe using ( just; nothing )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong )

open import Class.DecEq using ( DecEq; _≟_ )
import Class.DecEq.Instances as DecEqI

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeCliIoDec (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p
open import CSP.Examples.Cardano_network.Base using ( Dir; N2N_BlockFetch; FromInitiator )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl; τ*-step )

import CSP.Examples.Cardano_network.BlockFetch p as BF

import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA as SStep
open SStep using ( NetProc; absBFc; coarsenBFc; decBFc-sil-step )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA as SN
open SN using ( BFcPos; decBFc; bcHead; bcReq1; bcDone1; bcBlk1; bcSil )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-inv; nothing-absurd )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink6 blkA as SIL6
open SIL6 using ( Tbfc; mkMbfc
                ; bfc-fire-start; bfc-fire-noblk; bfc-fire-blk; bfc-fire-batch
                ; bfc-fire-req1; bfc-fire-cdone1 )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( BFcHasBlk )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeFillSource blkA
  using ( PlIsBlk )

------------------------------------------------------------------------
-- (1) THE io CLIENT-SUCCESSOR CLASSIFICATION.  Unlike the api case, an io CAN
-- deliver a block to the client — but only by READING one off the wire, so the
-- payload witnesses it.
------------------------------------------------------------------------

-- the io client-successor block classification: the successor is not holding,
-- or the payload the io carried was itself a block AND the read happened at the
-- CLIENT'S OWN key `(l,d)`.
--
-- SESSION-31 STRENGTHENING (the key pin).  The session-30 form dropped `l′`/`d′`,
-- and that is not enough for the consumer: `PipeInv.Coupled`'s client clause is
-- discharged from the CELL clause, which reads the cell at the LEG's own key
-- `(linkAB,hi,BF)` — so the fired label's key has to be identified with it.  The
-- pin is FREE here (the block branch already sits under `l′ ≟ l | d′ ≟ d`, both
-- `yes refl`); only carrying it was missing.
BfcIoSucc : (l : Link) (d : Dir) (l′ : Link) (d′ : Dir) → BFcPos → Payload → Set
BfcIoSucc l d l′ d′ bfc′ a = (BFcHasBlk bfc′ → ⊥) ⊎ ((l′ ≡ l) × (d′ ≡ d) × PlIsBlk a)

------------------------------------------------------------------------
-- (2) HEAD/SIL SLICE, `receiveBF` (the wire READ `output l d N2N_BlockFetch`).
-- BUSY reads StartBatch/NoBlocks (both ¬-block successors); STREAMING reads
-- `MsgBlock b` — landing on `bcBlk1 b`, the ONE block-gaining io — and
-- `MsgBatchDone`.  IDLE and DONE have no wire-read row.
------------------------------------------------------------------------

-- a `receiveBF` fire out of a BF-client HEAD: named successor + firing step +
-- abstract equality + the io block classification
bfc-recv-hstep : (l : Link) (d : Dir) (st : BF.BFState)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFc l d (bcHead st) ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► M
  → Σ[ bfc′ ∈ BFcPos ]
      (decBFc l d (bcHead st)
         ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► decBFc l d bfc′)
      × (M ≡ absBFc l d bfc′) × BfcIoSucc l d l′ d′ bfc′ a
-- IDLE / DONE heads: no wire-read row
bfc-recv-hstep l d BF.stIdle step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stDone step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- BUSY: StartBatch opens the stream, NoBlocks closes the batch; both ¬-block
bfc-recv-hstep l d BF.stBusy {l′} {d′} {a = t0 , md , ln , blockFetch MsgStartBatch} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bcSil BF.stStreaming , SIL6.RFBF.renameMap-ev-fwd (bfc-fire-start l d t0 md ln)
      , mkMbfc l d (bcSil BF.stStreaming) Meq (just-injective (sym ceq)) , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {l′} {d′} {a = t0 , md , ln , blockFetch MsgNoBlocks} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bcSil BF.stIdle , SIL6.RFBF.renameMap-ev-fwd (bfc-fire-noblk l d t0 md ln)
      , mkMbfc l d (bcSil BF.stIdle) Meq (just-injective (sym ceq)) , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {a = _ , _ , _ , blockFetch (MsgRequestRange r)} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {a = _ , _ , _ , blockFetch (MsgBlock b)} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {a = _ , _ , _ , blockFetch MsgBatchDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {a = _ , _ , _ , blockFetch MsgClientDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {a = _ , _ , _ , chainSync _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stBusy {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- STREAMING: the block read (the ONE block-gaining io) and the batch close
bfc-recv-hstep l d BF.stStreaming {l′} {d′} {a = t0 , md , ln , blockFetch (MsgBlock b)} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bcBlk1 b , SIL6.RFBF.renameMap-ev-fwd (bfc-fire-blk l d b t0 md ln)
      , mkMbfc l d (bcBlk1 b) Meq (just-injective (sym ceq)) , inj₂ (refl , refl , tt)
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {l′} {d′} {a = t0 , md , ln , blockFetch MsgBatchDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bcSil BF.stIdle , SIL6.RFBF.renameMap-ev-fwd (bfc-fire-batch l d t0 md ln)
      , mkMbfc l d (bcSil BF.stIdle) Meq (just-injective (sym ceq)) , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {a = _ , _ , _ , blockFetch (MsgRequestRange r)} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {a = _ , _ , _ , blockFetch MsgStartBatch} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {a = _ , _ , _ , blockFetch MsgNoBlocks} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {a = _ , _ , _ , blockFetch MsgClientDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {a = _ , _ , _ , chainSync _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-recv-hstep l d BF.stStreaming {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- (3) HEAD/SIL SLICE, `sendBF` (the wire WRITE `input l d N2N_BlockFetch`).
-- No head writes: the client's two writes sit at the dedicated `bcReq1`/
-- `bcDone1` positions, handled in (4).
------------------------------------------------------------------------

-- a `sendBF` fire out of a BF-client HEAD is impossible (no table row)
bfc-send-hstep : (l : Link) (d : Dir) (st : BF.BFState)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFc l d (bcHead st) ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► M
  → ⊥
bfc-send-hstep l d BF.stIdle step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = nothing-absurd ceq
bfc-send-hstep l d BF.stBusy step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = nothing-absurd ceq
bfc-send-hstep l d BF.stStreaming step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = nothing-absurd ceq
bfc-send-hstep l d BF.stDone step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = nothing-absurd ceq

------------------------------------------------------------------------
-- (4) THE TWO WHOLE-POSITION io DECODES.  Both deliver the `BFcDecode`-shaped
-- package (successor + concrete WEAK run + abstract equality) plus the io
-- block classification.  The wire WRITE is unconditionally ¬-block.
------------------------------------------------------------------------

-- a BF client firing the wire WRITE io: successor is a `bcSil`, hence ¬-block
decBFc-sendBF-succ : (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFc l d bfc ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► M
  → Σ[ bfc′ ∈ BFcPos ]
      (decBFc l d bfc ═[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]═► decBFc l d bfc′)
      × (M ≡ absBFc l d bfc′) × (BFcHasBlk bfc′ → ⊥)
decBFc-sendBF-succ l d (bcHead st) step = ⊥-elim (bfc-send-hstep l d st step)
decBFc-sendBF-succ l d (bcSil st)  step = ⊥-elim (bfc-send-hstep l d st step)
decBFc-sendBF-succ l d (bcBlk1 b) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-sendBF-succ l d (bcReq1 r) {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl
      with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | yes refl =
          bcSil BF.stBusy
        , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfc-fire-req1 l d r)) τ*-refl
        , mkMbfc l d (bcSil BF.stBusy) Meq (just-injective (sym ceq)) , (λ ())
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-sendBF-succ l d (bcReq1 r) step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-sendBF-succ l d (bcReq1 r) step | q′ , ceq , Meq | no _    | _    = ⊥-elim (nothing-absurd ceq)
decBFc-sendBF-succ l d bcDone1 {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl
      with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | yes refl =
          bcSil BF.stDone
        , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfc-fire-cdone1 l d)) τ*-refl
        , mkMbfc l d (bcSil BF.stDone) Meq (just-injective (sym ceq)) , (λ ())
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-sendBF-succ l d bcDone1 step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-sendBF-succ l d bcDone1 step | q′ , ceq , Meq | no _    | _    = ⊥-elim (nothing-absurd ceq)

-- a BF client firing the wire READ io: `bcBlk1 b` only when the payload IS a block
decBFc-receiveBF-succ : (l : Link) (d : Dir) (bfc : BFcPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFc l d bfc ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► M
  → Σ[ bfc′ ∈ BFcPos ]
      (decBFc l d bfc ═[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]═► decBFc l d bfc′)
      × (M ≡ absBFc l d bfc′) × BfcIoSucc l d l′ d′ bfc′ a
decBFc-receiveBF-succ l d (bcHead st) step with bfc-recv-hstep l d st step
... | bfc′ , f , m , cls = bfc′ , wev τ*-refl f τ*-refl , m , cls
decBFc-receiveBF-succ l d (bcSil st) step with bfc-recv-hstep l d st step
... | bfc′ , f , m , cls =
      bfc′ , wev (τ*-step (decBFc-sil-step l d st) τ*-refl) f τ*-refl , m , cls
decBFc-receiveBF-succ l d (bcReq1 r) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-receiveBF-succ l d bcDone1 step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-receiveBF-succ l d (bcBlk1 b) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the io BUNDLE EVOLUTION exposer
-- (`Praos.PipeBundleIoEvo`), the THREADING half of sub-obligation (b) of the
-- `PipeInvProd.TauIoS` arm.
--
-- `WalkConvNodeDrop.absBundleG-io-prod-wt` inverts an io fire of a 12-peer
-- bundle but binds the FIVE successor slots EXISTENTIALLY inside `bgEBwt`, and
-- `absBundleG` has no slot injectivity, so a SECOND independent peel of the
-- same step cannot be tied to the first (session-30 measured negative result).
-- ((T5, review M-4) read "`absBundleG` has no slot injectivity" as the SLOT-level
-- statement it is: it is about THIS decomposition, not about tables.  Coarse
-- `tableSpec` position injectivity IS derivable — `LiveCSRow` §2/§3 proves it for both
-- ChainSync tables — so the absolute phrasing the T3/T4 reversal refuted must not be
-- read back into this sentence.)
-- Hence the bundle inversion has to be RE-DERIVED carrying, in ONE result, the
-- successor slots TOGETHER with the two BF evolutions.
--
-- THE ECONOMY (this is why the leaf is ~300 lines and not the ~950 the session
-- -30 note budgeted).  Reading the CONSUMERS first showed that almost all of
-- the cascade already exists in a REUSABLE, `e₁`-GENERIC form:
--
--   · the FIVE non-BF 12-peer cascades `SysIoLink6.absBundle{CS,KA,TS,LN,LF}
--     -ev-prod` are generic in `e₁` and are ALREADY the ones the frozen io
--     dispatcher `absBundleG-io-prod` calls — their results keep BOTH BF slots
--     LITERAL, so lifting them into the new result is a two-clause `inj₁ refl`
--     wrapper each.  NO re-mirror at all for 10 of the 12 peers.
--   · only the BF cascade needs re-deriving, and even that is a copy of
--     `PipeBundleEvo.absBundleBF-ev-evo` (already generic in `e₁` and already
--     callback-parametric) with its two hard-wired block facts replaced by two
--     ABSTRACT predicates `Cf`/`Sf`.  Abstracting them is what lets the SAME
--     cascade serve the api client fact `(BFcHasBlk bfc′ → ⊥)` and the io one
--     `BfcIoSucc bfc′ a` — the api form is genuinely unsatisfiable on an io
--     (`bcStream --output … MsgBlock b--> bcAblk b`, `NodeSpecs.bfCnxt`:544).
--
-- The client arm is stated with `BlkReadAt`, the label-directed BF-wire-READ
-- classifier, so that the result can live at the dispatcher's GENERIC carrier
-- `X` (a BF io label pins `X ≡ Payload`, every other constructor gives `⊥`) AND
-- so that the fired key is identified with the CLIENT'S OWN `(l,cl)` — without
-- that pin the consumer cannot tie the read to the leg's own medium cell.
--
-- The two io decodes are last session's green leaves `PipeCliIoDec` (client)
-- and `PipeSrvIoDec` (server); `BfsSucc`'s left disjunct is the whole server
-- answer, so the server arm here is the plain `BFsHasBlk bfs′ → ⊥`.
--
-- Imported by nothing yet.  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; cong; trans; sym; _≢_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleIoEvo (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; N2N_ChainSync; N2N_BlockFetch; N2N_KeepAlive
  ; N2N_TxSubmission; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; done; input; output
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack; break )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιCS; ιBF; ιKA; ιTS; ιLN; ιLF )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _⦀_; EventSet ) renaming ( ∅ES to ∅ESa )
open EventSet using ( mem )

import CSP.Examples.Cardano_network.ChainSync p as CS
import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Examples.Cardano_network.KeepAlive p as KA
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.LeiosNotify p as LN
import CSP.Examples.Cardano_network.LeiosFetch p as LF

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using
  ( NetProc; absBundleG; absKAc; absKAs; absCSc; absCSs; absBFc; absBFs
  ; absTSc; absTSs; absLNc; absLNs; absLFc; absLFs )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using
  ( CScPos; CSsPos; BFcPos; BFsPos; InertPos; kac; kas; tsc; tss; lnc; lns; lfc; lfs
  ; bundleG; decKAc; decKAs; decCSc; decCSs; decBFc; decBFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA using
  ( noOffer→viewV
  ; decKAc-noOffer; decKAs-noOffer; ιKA⁻¹∘ιBF
  ; decCSc-noBFgen; decCSs-noBFgen; decBFc-dir-noOffer
  ; bfTail-bfs-noOffer; bfTail-tsc-noOffer
  ; absKAc-noBF; absKAs-noBF; absCSc-noBF; absCSs-noBF; absTSc-noBF; absTSs-noBF
  ; absLNc-noBF; absLNs-noBF; absLFc-noBF; absLFs-noBF
  ; absBFs-dir-noBoth )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA as SIL6
open SIL6 using
  ( ⦀-wev-L; ⦀-wev-R; absBFc-ev-dir; absBFs-ev-dir
  ; BundleCSEvR-abs; bcscEB; bcssEB
  ; BundleKAEvR-abs; bkacEB; bkasEB
  ; BundleTSEvR-abs; btscEB; btssEB
  ; BundleLNEvR-abs; blncEB; blnsEB
  ; BundleLFEvR-abs; blfcEB; blfsEB
  ; absBundleCS-ev-prod; absBundleKA-ev-prod; absBundleTS-ev-prod
  ; absBundleLN-ev-prod; absBundleLF-ev-prod )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA using
  ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA using
  ( PlIsBlk )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeCliIoDec blkA as CLI
open CLI using ( BfcIoSucc; CliBlkVal; decBFc-sendBF-succ; decBFc-receiveBF-succ )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvIoDec blkA as SRV
open SRV using ( decBFs-sendBF-succ; decBFs-receiveBF-succ )

------------------------------------------------------------------------
-- (1) THE LABEL-DIRECTED PAYLOAD CLASSIFIER.  The bundle result lives at the
-- dispatcher's generic carrier `X`, but "the io payload was a block" only makes
-- sense at `X ≡ Payload`; matching the label constructor performs exactly that
-- refinement (`input`/`output` are the two io shapes; everything else is `⊥`).
------------------------------------------------------------------------

-- "the io event `e` is a BF wire READ at the key `(l,d)` and the value `a` it
-- carried is a fetched block".  The key pin is what lets the consumer identify
-- the touched medium cell with the leg's own `cellUp`/`cellDn`; every other
-- label shape (including a BF wire WRITE, on which a client never gains a
-- block) is `⊥`.
-- SESSION-36: indexed by the SUCCESSOR position `q` as well, so the block arm
-- can name which block the reader ended up holding (`PipeCliIoDec.CliBlkVal`).
-- The index is free: `BFcDecodeP`'s client fact is already applied to the
-- successor, so `bfEvRio→g` just passes `z` along.
BlkReadAt : (l : Link) (d : Dir) (q : BFcPos) {X : Set 0ℓ} → Net_Api Payload X → X → Set
BlkReadAt l d q (output l′ d′ N2N_BlockFetch)   a =
  (l′ ≡ l) × (d′ ≡ d) × (PlIsBlk a × CliBlkVal q a)
BlkReadAt l d q (output _  _  N2N_ChainSync)    _ = ⊥
BlkReadAt l d q (output _  _  N2N_TxSubmission) _ = ⊥
BlkReadAt l d q (output _  _  N2N_KeepAlive)    _ = ⊥
BlkReadAt l d q (output _  _  N2N_LeiosNotify)  _ = ⊥
BlkReadAt l d q (output _  _  N2N_LeiosFetch)   _ = ⊥
BlkReadAt l d q (input  _ _ _) _ = ⊥
BlkReadAt l d q (sndmsg _ _ _) _ = ⊥
BlkReadAt l d q (rcvmsg _ _ _) _ = ⊥
BlkReadAt l d q (tx     _ _ _) _ = ⊥
BlkReadAt l d q (sndack _ _ _) _ = ⊥
BlkReadAt l d q (rcvack _ _ _) _ = ⊥
BlkReadAt l d q (ack    _ _ _) _ = ⊥
BlkReadAt l d q (done   _ _ _) _ = ⊥
BlkReadAt l d q (apiCS  _ _ _) _ = ⊥
BlkReadAt l d q (apiBF  _ _ _) _ = ⊥
BlkReadAt l d q (apiTS  _ _ _) _ = ⊥
BlkReadAt l d q (apiKA  _ _ _) _ = ⊥
BlkReadAt l d q (apiLN  _ _ _) _ = ⊥
BlkReadAt l d q (apiLF  _ _ _) _ = ⊥
BlkReadAt l d q (break  _)     _ = ⊥

------------------------------------------------------------------------
-- (2) THE BF CASCADE, PREDICATE-PARAMETRIC.  A copy of
-- `PipeBundleEvo.absBundleBF-ev-evo` whose two hard-wired block facts are
-- replaced by abstract `Cf`/`Sf`, so the SAME 12-peer peel serves the api
-- client fact and the io one.  Nothing else changes: the ten sibling
-- refutations and the `⦀-wev` tower are verbatim.
------------------------------------------------------------------------

-- the caller-supplied isolated-client decode, at an abstract client fact `Cf`
BFcDecodeP : (l : Link) (cl : Dir) (bfc : BFcPos) (Cf : BFcPos → Set)
             {X : Set 0ℓ} (e₁ : BF.BFEv X) (a : X) → Set₁
BFcDecodeP l cl bfc Cf {X} e₁ a =
  ∀ {P′ : NetProc} → absBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → Σ[ bfc′ ∈ BFcPos ]
      (decBFc l cl bfc ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFc l cl bfc′)
      × (P′ ≡ absBFc l cl bfc′) × Cf bfc′

-- the caller-supplied isolated-server decode, at an abstract server fact `Sf`
BFsDecodeP : (l : Link) (sv : Dir) (bfs : BFsPos) (Sf : BFsPos → Set)
             {X : Set 0ℓ} (e₁ : BF.BFEv X) (a : X) → Set₁
BFsDecodeP l sv bfs Sf {X} e₁ a =
  ∀ {P′ : NetProc} → absBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l sv bfs ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFs l sv bfs′)
      × (P′ ≡ absBFs l sv bfs′) × Sf bfs′

-- which driven BF peer fired + its updated slot + the concrete weak run + the
-- abstract fact for that slot (the non-fired BF slot stays LITERAL)
data BundleBFEvRio (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     (Cf : BFcPos → Set) (Sf : BFsPos → Set)
     {X : Set 0ℓ} (e₁ : BF.BFEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bioCli : (bfc′ : BFcPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc′ bfs ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► bundleG l cl sv csc css bfc′ bfs ip
        → Cf bfc′
        → BundleBFEvRio l cl sv csc css bfc bfs ip Cf Sf e₁ a Bd′
  bioSrv : (bfs′ : BFsPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs′ ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► bundleG l cl sv csc css bfc bfs′ ip
        → Sf bfs′
        → BundleBFEvRio l cl sv csc css bfc bfs ip Cf Sf e₁ a Bd′

-- fold a decoded BF-client fire into the bundle result (mirror `finishBFc⁺`)
finishBFc-io : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    (Cf : BFcPos → Set) (Sf : BFsPos → Set)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → (sM : absBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′)
  → Σ[ bfc′ ∈ BFcPos ]
      (decBFc l cl bfc ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFc l cl bfc′)
      × (P′ ≡ absBFc l cl bfc′) × Cf bfc′
  → BundleBFEvRio l cl sv csc css bfc bfs ip Cf Sf e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (P′
        ⦀ (absBFs l sv bfs ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishBFc-io l cl sv csc css bfc bfs ip Cf Sf {e₁ = e₁} cl≢sv sM (bfc′ , run , Meq , cf) =
      bioCli bfc′
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (z
               ⦀ (absBFs l sv bfs ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁)))
            (⦀-wev-R (decCSc l cl csc) _
              (noOffer→viewV (decCSc l cl csc) (decCSc-noBFgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _
                (noOffer→viewV (decCSs l sv css) (decCSs-noBFgen l sv css e₁))
                (⦀-wev-L (decBFc l cl bfc) _
                  (noOffer→viewV _
                    (bfTail-bfs-noOffer l cl sv bfs ip e₁
                      (λ q → cl≢sv (trans (sym (absBFc-ev-dir l cl bfc sM)) q))))
                  run)))))
        cf

-- fold a decoded BF-server fire into the bundle result (mirror `finishBFs⁺`)
finishBFs-io : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    (Cf : BFcPos → Set) (Sf : BFsPos → Set)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → (sM : absBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′)
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l sv bfs ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFs l sv bfs′)
      × (P′ ≡ absBFs l sv bfs′) × Sf bfs′
  → BundleBFEvRio l cl sv csc css bfc bfs ip Cf Sf e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (P′
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishBFs-io l cl sv csc css bfc bfs ip Cf Sf {e₁ = e₁} cl≢sv sM (bfs′ , run , Meq , sf) =
      bioSrv bfs′
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (z
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁)))
            (⦀-wev-R (decCSc l cl csc) _
              (noOffer→viewV (decCSc l cl csc) (decCSc-noBFgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _
                (noOffer→viewV (decCSs l sv css) (decCSs-noBFgen l sv css e₁))
                (⦀-wev-R (decBFc l cl bfc) _
                  (noOffer→viewV (decBFc l cl bfc)
                    (decBFc-dir-noOffer l cl bfc e₁ (λ q → cl≢sv (trans (sym q) (absBFs-ev-dir l sv bfs sM)))))
                  (⦀-wev-L (decBFs l sv bfs) _
                    (noOffer→viewV _ (bfTail-tsc-noOffer l cl sv ip e₁))
                    run))))))
        sf

-- the 12-peer BF bundle inversion at abstract client/server facts (mirror
-- `PipeBundleEvo.absBundleBF-ev-evo`; the ten sibling refutations are verbatim)
absBundleBF-ev-io-evo : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     → (Cf : BFcPos → Set) (Sf : BFsPos → Set)
     → {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
     → BFcDecodeP l cl bfc Cf e₁ a
     → BFsDecodeP l sv bfs Sf e₁ a
     → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
     → BundleBFEvRio l cl sv csc css bfc bfs ip Cf Sf e₁ a Bd′
absBundleBF-ev-io-evo l cl sv cl≢sv csc css bfc bfs ip Cf Sf {X} {e₁} {a} kc ks step
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
...         | PEA.evL _ sM = finishBFc-io l cl sv csc css bfc bfs ip Cf Sf cl≢sv sM (kc sM)
...         | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-dir-noBoth l sv bfs e₁ (λ q → cl≢sv (trans (sym (absBFc-ev-dir l cl bfc sM)) q))) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁)))))) (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = finishBFs-io l cl sv csc css bfc bfs ip Cf Sf cl≢sv sM (ks sM)
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
-- (3) THE UNIFIED io RESULT and its six per-channel lifters.  The five non-BF
-- channels reuse the FROZEN `absBundleX-ev-prod` cascades verbatim: their
-- results keep BOTH BF slots LITERAL, so both arms are `inj₁ refl`.
------------------------------------------------------------------------

-- the io bundle inversion with BOTH BF evolutions: successor slots + concrete
-- weak run + the client arm (fixed / not-holding / the payload WAS a block) +
-- the server arm (fixed / not-holding)
data BundleGEvRio⁺ (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) (Bd′ : NetProc) : Set₁ where
  bgEBio⁺ : (csc′ : CScPos) (css′ : CSsPos) (bfc′ : BFcPos) (bfs′ : BFsPos) (ip′ : InertPos)
       → Bd′ ≡ absBundleG l cl sv csc′ css′ bfc′ bfs′ ip′
       → bundleG l cl sv csc css bfc bfs ip
           ═[ ev (evl (evLabel X e a)) ]═► bundleG l cl sv csc′ css′ bfc′ bfs′ ip′
       → ((bfc ≡ bfc′) ⊎ ((BFcHasBlk bfc′ → ⊥) ⊎ BlkReadAt l cl bfc′ e a))
       → ((bfs ≡ bfs′) ⊎ (BFsHasBlk bfs′ → ⊥))
       → BundleGEvRio⁺ l cl sv csc css bfc bfs ip e a Bd′

-- CS lifter (both BF slots literal)
csEvR→gio : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → BundleCSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvRio⁺ l cl sv csc css bfc bfs ip (ιCS e₁) a Bd′
csEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (bcscEB csc′ eq run) = bgEBio⁺ csc′ css  bfc bfs ip eq run (inj₁ refl) (inj₁ refl)
csEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (bcssEB css′ eq run) = bgEBio⁺ csc  css′ bfc bfs ip eq run (inj₁ refl) (inj₁ refl)

-- KA lifter (both BF slots literal)
kaEvR→gio : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
  → BundleKAEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvRio⁺ l cl sv csc css bfc bfs ip (ιKA e₁) a Bd′
kaEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (bkacEB kac′ eq run) = bgEBio⁺ csc css bfc bfs (record ip { kac = kac′ }) eq run (inj₁ refl) (inj₁ refl)
kaEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (bkasEB kas′ eq run) = bgEBio⁺ csc css bfc bfs (record ip { kas = kas′ }) eq run (inj₁ refl) (inj₁ refl)

-- TS lifter (both BF slots literal)
tsEvR→gio : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {Bd′ : NetProc}
  → BundleTSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvRio⁺ l cl sv csc css bfc bfs ip (ιTS e₁) a Bd′
tsEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (btscEB tsc′ eq run) = bgEBio⁺ csc css bfc bfs (record ip { tsc = tsc′ }) eq run (inj₁ refl) (inj₁ refl)
tsEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (btssEB tss′ eq run) = bgEBio⁺ csc css bfc bfs (record ip { tss = tss′ }) eq run (inj₁ refl) (inj₁ refl)

-- LN lifter (both BF slots literal)
lnEvR→gio : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {Bd′ : NetProc}
  → BundleLNEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvRio⁺ l cl sv csc css bfc bfs ip (ιLN e₁) a Bd′
lnEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (blncEB lnc′ eq run) = bgEBio⁺ csc css bfc bfs (record ip { lnc = lnc′ }) eq run (inj₁ refl) (inj₁ refl)
lnEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (blnsEB lns′ eq run) = bgEBio⁺ csc css bfc bfs (record ip { lns = lns′ }) eq run (inj₁ refl) (inj₁ refl)

-- LF lifter (both BF slots literal)
lfEvR→gio : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {Bd′ : NetProc}
  → BundleLFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvRio⁺ l cl sv csc css bfc bfs ip (ιLF e₁) a Bd′
lfEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (blfcEB lfc′ eq run) = bgEBio⁺ csc css bfc bfs (record ip { lfc = lfc′ }) eq run (inj₁ refl) (inj₁ refl)
lfEvR→gio {csc = csc} {css} {bfc} {bfs} {ip} (blfsEB lfs′ eq run) = bgEBio⁺ csc css bfc bfs (record ip { lfs = lfs′ }) eq run (inj₁ refl) (inj₁ refl)

-- BF lifter: the fired BF slot carries its fact, the other stays literal
bfEvRio→g : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → BundleBFEvRio l cl sv csc css bfc bfs ip
      (λ z → (BFcHasBlk z → ⊥) ⊎ BlkReadAt l cl z (ιBF e₁) a) (λ z → BFsHasBlk z → ⊥) e₁ a Bd′
  → BundleGEvRio⁺ l cl sv csc css bfc bfs ip (ιBF e₁) a Bd′
bfEvRio→g {csc = csc} {css} {bfc} {bfs} {ip} (bioCli bfc′ eq run cf) = bgEBio⁺ csc css bfc′ bfs  ip eq run (inj₂ cf)    (inj₁ refl)
bfEvRio→g {csc = csc} {css} {bfc} {bfs} {ip} (bioSrv bfs′ eq run sf) = bgEBio⁺ csc css bfc  bfs′ ip eq run (inj₁ refl) (inj₂ sf)

------------------------------------------------------------------------
-- (4) THE io DISPATCHER — the shape `PipeInvProd.TauIoS`'s node cone consumes.
-- Mirror of `SysIoLink6.absBundleG-io-prod`: case on the raw io event, invoke
-- the channel's cascade, lift.  The BF arms route the fired peer through last
-- session's io decodes (`PipeCliIoDec` / `PipeSrvIoDec`); the client's wire
-- WRITE is unconditionally ¬-block (`inj₁`), its wire READ is the genuine
-- disjunction.
------------------------------------------------------------------------

-- unified io bundle dispatcher with BOTH BF evolutions
absBundleG-io-evo : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → BundleGEvRio⁺ l cl sv csc css bfc bfs ip e a Bd′
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_ChainSync}    iomem step = csEvR→gio (absBundleCS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.sendCS    l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_ChainSync}    iomem step = csEvR→gio (absBundleCS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.receiveCS l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_BlockFetch}   iomem step =
  bfEvRio→g (absBundleBF-ev-io-evo l cl sv cl≢sv csc css bfc bfs ip _ _ {e₁ = BF.sendBF l′ d′}
    (λ sM → let (bfc′ , run , Meq , nb) = decBFc-sendBF-succ l cl bfc sM in bfc′ , run , Meq , inj₁ nb)
    (decBFs-sendBF-succ l sv bfs) step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_BlockFetch}   iomem step =
  bfEvRio→g (absBundleBF-ev-io-evo l cl sv cl≢sv csc css bfc bfs ip _ _ {e₁ = BF.receiveBF l′ d′}
    (decBFc-receiveBF-succ l cl bfc)
    (decBFs-receiveBF-succ l sv bfs) step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_KeepAlive}    iomem step = kaEvR→gio (absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.sendKA    l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_KeepAlive}    iomem step = kaEvR→gio (absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.receiveKA l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_TxSubmission} iomem step = tsEvR→gio (absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.sendTS    l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_TxSubmission} iomem step = tsEvR→gio (absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.receiveTS l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosNotify}  iomem step = lnEvR→gio (absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.sendLN    l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosNotify}  iomem step = lnEvR→gio (absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.receiveLN l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = input  l′ d′ N2N_LeiosFetch}   iomem step = lfEvR→gio (absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.sendLF    l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosFetch}   iomem step = lfEvR→gio (absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.receiveLF l′ d′} step)
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = done   _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiCS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiBF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiKA  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiTS  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiLN  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiLF  _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} iomem step = ⊥-elim iomem
absBundleG-io-evo l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     iomem step = ⊥-elim iomem

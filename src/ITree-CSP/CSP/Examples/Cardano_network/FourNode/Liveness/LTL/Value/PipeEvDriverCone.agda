{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the GENUINE-Adv DRIVER-STEP EXPOSURE CONE
-- (`Praos.PipeEvDriverCone`).
--
-- `PipeNodeFixApi.top-nodes-abs-expose-cls` classifies a visible api-CSBF middle
-- into the whole-`μTot` drop + the permissive per-driver `ProdClass1`/
-- `RelayClass1` + the whole-nodes client classifier.  But `PipeEvDriver`'s
-- preservation glue needs the GENUINE `WalkMeasure` driver families, not the
-- permissive advance algebras:
--   · node A producer  → `WalkMeasure.ProdAdv` (`padv`, from `naEBawt`);
--   · node D consumer  → `WalkMeasure.ConsAdv` (`cadv`) + the `cp3 → recvBFBlock`
--     label witness (`lblD`);
--   · node B/C relay   → the ISOLATED `decCP` step, classified by
--     `PipeEvRelay.cpStepKind-of` into a `RelayStepKind` (the `consuming cp6`
--     composite is NOT a single `CPAdv`, so a raw `RelayStepKind` is exposed).
--
-- THIS module re-mirrors the per-node api peels of `PipeNodeFixApi`
-- (`nodeB/C-api-*-abs-cls`, `nodeD-api-*-abs-cls`) RETAINING those genuine
-- families and DROPPING the `cpW`/`μTot` legs + the client classifier.  Node A
-- is REUSED wholesale from `WalkApiDrop.nodeA-ev-api-abs-wt` (its `naEBawt`
-- already carries the genuine `padv`).  The whole-nodes dispatch
-- `driverExpose` assembles, for BOTH delivery legs, a `LegDriverStep` sum:
-- either the firing driver's genuine advance (with the ambient component
-- FIXITIES the matching `pres-*` demands) or leg-wide FIXITY.
--
-- Because each successor node is built with LITERAL non-firing fields, every
-- non-firing component equality is `refl` DEFINITIONALLY; the only non-`refl`
-- fixity is node A's own OTHER-leg producer (`pACeq`/`pABeq`).
--
-- LIGHT-to-medium (Par-ev-elim plumbing across 4 nodes, but no `μTot`
-- arithmetic).  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriverCone (blkA : Block₃) where

open import Level using (0ℓ)
open import Data.Product using ( _,_; Σ; _×_; Σ-syntax; proj₁; proj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; cong; trans; sym; subst )
open import Data.Sum using ( inj₁; inj₂; _⊎_ )
open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; EventSet; viewV )
open EventSet using ( mem )
open Op using () renaming ( ∅ES to ∅ESa )

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; ⦀-ev-L; ⦀-ev-R )

open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )
open import CSP.Examples.Cardano_network.Net p using ( Link; apiBF; recvBFBlock )
open SStep using
  ( absBundleG; absNodeA; absNodeB; absNodeC; absNodeD )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using
  ( ProdPh; ConsPh; CPPh; consuming; producing; consD; cph; cblk; cp3 )
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( ApiHasLink; apiLink-inj; ahlBF
  ; decConsD-ev-link; decCP-ev-link )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA using
  ( absNodeA-fp; absNodeB-fp; absNodeC-fp; absNodeD-fp
  ; nodeB-no-when-A; nodeC-no-when-A; nodeD-no-when-A; nodeC-no-when-B; nodeD-no-when-B; nodeD-no-when-C
  ; absNodeB-no-when-A; absNodeC-no-when-A; absNodeD-no-when-A; absNodeC-no-when-B; absNodeD-no-when-B; absNodeD-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA using
  ( linkAB≢linkAC; linkAB≢linkBD; linkAC≢linkCD; linkBD≢linkCD )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( ⦀-wev-L; ⦀-wev-R; ∥⇘⇙-wev-sync
        ; ev→wev
        ; bgEB
        ; absBundleG-api-prod; absBundleG-api-no; bundleG-api-no
        ; drvD-CD-no; drvD-BD-no
        ; nodeA-no-when-B; nodeA-no-when-C; nodeA-no-when-D
        ; nodeB-no-when-C; nodeB-no-when-D; nodeC-no-when-D )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkClassify blkA using
  ( consDAdv-of; consD-c34-lbl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA using
  ( ProdAdv; ConsAdv; c01; c12; c23; c34; c45; c56 )

-- the genuine driver-step consumers this cone feeds
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriver blkA using
  ( RelayStepKind )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvRelay blkA using
  ( cpStepKind-of; cpStepKindL-of )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( prodOf; relayOf; cellUp; cellDn; upClient; dnClient
  ; RelayPre; RelayHas; RelayFwd; ConsRecv; ProdSent; BFcHasBlk )
-- SESSION-33 (G2c): the BF-SERVER slots + their maximal evolution witnesses
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA using
  ( upSrv; dnSrv; UpSrvEvo; DnSrvEvo )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeProdFire blkA using
  ( IsSBB )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA using
  ( TwoLegs; legBD; legCD; phOf; linkOf; InCp03; cblkOf )
-- SESSION-40: the VALUE-ANCHORED node-D classifier (the delivering label pinned
-- at the SAME successor block), so `ldCons` can carry `cblkOf l s′ ≡ b″`
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor blkA using
  ( consDAdv-of⁺; ConsHeld )
-- SESSION-51: the per-component VALUE classifiers the appended `LegValStep`
-- reports at (`PipeVal`'s clauses (1)/(4)/(5)/(8) are the four `LegDriverStep`
-- does not carry)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA using
  ( RelayValOK )
-- SESSION-41: the bundle-level client-POSITION pin, so `ldCons` can also carry
-- `dnClient l s ≡ bcBlk1 b″` — the value-blind `wDn` cannot
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA using
  ( bundle-recv-cliPos )
-- SESSION-45: the value-carrying relay classifier — its label component names
-- the SUCCESSOR's shape, so `wUp` can report the relayed block
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValRelay blkA using
  ( cpStepKindL-of⁺; RelayAt )

-- the receive-coupling feeders (session-26 cone-witness extension)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleRecv blkA using
  ( bundle-recvBFBlock-forces-src )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA using
  ( BundleGEvR⁺; bgEB⁺; absBundleG-api-evo; BFsHasBlk; BfsSucc )

-- node A: the SESSION-33 re-mirror on `absBundleG-api-evo` (the frozen
-- `WalkApiDrop.nodeA-ev-api-abs-wt` drops the BF-server slot `SrvCoupled` reads)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeAEvo blkA using
  ( NodeAEvR-abs-evo; naEBaev1; naEBaev2; nodeA-ev-api-abs-evo )

------------------------------------------------------------------------
-- SESSION-33 (G2c): fold a raw `bgEB⁺` SERVER slot (at a relay's PRODUCE-leg
-- bundle) into the `PipeSrvInv.DnSrvEvo` shape.  The block arm's label pin IS
-- the co-firing relay driver's `pp5 → pp6` fire, which `cpStepKindL-of`'s
-- SESSION-33 field turns into `RelayFwd` of the successor phase.
------------------------------------------------------------------------

-- resolve a produce-leg server evolution into `fixed ⊎ (¬holding ⊎ forwarded)`
srvEvo⇒fwd : {l : Link} {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
             (bfs bfs′ : SN.BFsPos) (x′ : CPPh)
           → (IsSBB (evLabel X e a) → RelayFwd x′)
           → ((bfs ≡ bfs′) ⊎ BfsSucc l hi bfs′ e a)
           → (bfs ≡ bfs′) ⊎ ((BFsHasBlk bfs′ → ⊥) ⊎ RelayFwd x′)
srvEvo⇒fwd bfs bfs′ x′ fwdR (inj₁ eq)                    = inj₁ eq
srvEvo⇒fwd bfs bfs′ x′ fwdR (inj₂ (inj₁ nb))             = inj₂ (inj₁ nb)
srvEvo⇒fwd bfs bfs′ x′ fwdR (inj₂ (inj₂ (b″ , lbl , _))) =
  inj₂ (inj₂ (fwdR (subst IsSBB (sym lbl) tt)))

------------------------------------------------------------------------
-- SESSION-51: the RAW server-evolution witness (`PipeBundleEvo`'s own shape,
-- BEFORE `srvEvo⇒up`/`srvEvo⇒fwd` project the block away) and the two per-leg
-- BF-server link keys.
------------------------------------------------------------------------

-- a BF server slot is either FIXED across the step, or entered `bsBlk1 b″` via
-- the pinned `sendBFBlock` fire (this is literally `absBundleG-api-evo`'s own
-- server output — no new fold, only a value to carry)
SrvValEvo : (l : Link) (bfs bfs′ : SN.BFsPos)
            {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set₁
SrvValEvo l bfs bfs′ e a = (bfs ≡ bfs′) ⊎ BfsSucc l hi bfs′ e a

-- the leg's UPSTREAM BF-server link (node A's sender); the downstream one is
-- `WalkPr.linkOf`
upLinkOf : TwoLegs → Link
upLinkOf legBD = linkAB
upLinkOf legCD = linkAC

------------------------------------------------------------------------
-- node-D genuine-consumer peel record: successor node, node weak run, the
-- genuine `ConsAdv`, the co-leg consume + client FIXITY (literal ⇒ `refl`),
-- the `cp3 → recvBFBlock` label witness, PLUS (session-26 cone-witness
-- extension) the firing leg's DOWNSTREAM-CLIENT EVOLUTION disjunct and the
-- receive-coupling `wDn` fact the `pres-cons` glue demands.
------------------------------------------------------------------------

-- the receive crossing pins the consumer source phase to `cp3` (every other
-- single adjacency refutes one antecedent)
consAdv-recv-src : ∀ {a b} → ConsAdv a b → InCp03 a → ConsRecv b → a ≡ cp3
consAdv-recv-src c01 _ ()
consAdv-recv-src c12 _ ()
consAdv-recv-src c23 _ ()
consAdv-recv-src c34 _ _ = refl
consAdv-recv-src c45 () _
consAdv-recv-src c56 () _

data NodeDDrv (nd : SN.NodeStateD) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (M : NetProc) : Set₁ where
  ndDrvBD : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
          → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
          → ConsAdv (cph (SN.NodeStateD.cons-BD nd)) (cph (SN.NodeStateD.cons-BD nd′))
          → SN.NodeStateD.cons-CD nd′ ≡ SN.NodeStateD.cons-CD nd
          → SN.NodeStateD.bfC-CD nd′ ≡ SN.NodeStateD.bfC-CD nd
          -- SESSION-40 ANCHOR: `b″` is the block the SUCCESSOR slot records
          → (cph (SN.NodeStateD.cons-BD nd) ≡ cp3
             → Σ[ b″ ∈ Block₃ ]
                 (evLabel X e a ≡ evLabel Block₃ (apiBF linkBD hi recvBFBlock) b″)
               × (cblk (SN.NodeStateD.cons-BD nd′) ≡ b″)
               -- SESSION-41: and the CO-FIRING client held exactly that block
               × (SN.NodeStateD.bfC-BD nd ≡ SN.bcBlk1 b″))
          → ((SN.NodeStateD.bfC-BD nd ≡ SN.NodeStateD.bfC-BD nd′)
             ⊎ (BFcHasBlk (SN.NodeStateD.bfC-BD nd′) → ⊥))
          → (InCp03 (cph (SN.NodeStateD.cons-BD nd)) → ConsRecv (cph (SN.NodeStateD.cons-BD nd′))
             → BFcHasBlk (SN.NodeStateD.bfC-BD nd))
          -- SESSION-51: PAST the receive the recorded block is FIXED
          → (ConsHeld (cph (SN.NodeStateD.cons-BD nd))
             → cblk (SN.NodeStateD.cons-BD nd′) ≡ cblk (SN.NodeStateD.cons-BD nd))
          -- SESSION-56 (owner grant #5, (P8)): THE FIRING CONSUME-DRIVER STEP
          -- ITSELF, at this leg's own source and successor slots.  The peel below
          -- already holds it (`sDBD`) and threw it away.  It is the ONE witness a
          -- consumer of this record cannot rebuild: from it `decConsD-ev-link`
          -- gives the FIRED LINK (without which the co-leg's `ldFix` arm is
          -- unrefutable) and a `recvBFBlock` table inversion gives the `≡ cp3`
          -- GATE the SESSION-40 anchor above is conditioned on (without which
          -- that anchor is dead).  Strictly additive: every existing field keeps
          -- its meaning and position.
          → (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)
               ─[ ev (evl (evLabel X e a)) ]─►
               SN.decConsD linkBD (SN.NodeStateD.cons-BD nd′))
          → NodeDDrv nd e a M
  ndDrvCD : (nd′ : SN.NodeStateD) → M ≡ absNodeD nd′
          → SN.decNodeD nd ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeD nd′
          → ConsAdv (cph (SN.NodeStateD.cons-CD nd)) (cph (SN.NodeStateD.cons-CD nd′))
          → SN.NodeStateD.cons-BD nd′ ≡ SN.NodeStateD.cons-BD nd
          → SN.NodeStateD.bfC-BD nd′ ≡ SN.NodeStateD.bfC-BD nd
          -- SESSION-40 ANCHOR (mirror)
          → (cph (SN.NodeStateD.cons-CD nd) ≡ cp3
             → Σ[ b″ ∈ Block₃ ]
                 (evLabel X e a ≡ evLabel Block₃ (apiBF linkCD hi recvBFBlock) b″)
               × (cblk (SN.NodeStateD.cons-CD nd′) ≡ b″)
               -- SESSION-41 (mirror)
               × (SN.NodeStateD.bfC-CD nd ≡ SN.bcBlk1 b″))
          → ((SN.NodeStateD.bfC-CD nd ≡ SN.NodeStateD.bfC-CD nd′)
             ⊎ (BFcHasBlk (SN.NodeStateD.bfC-CD nd′) → ⊥))
          → (InCp03 (cph (SN.NodeStateD.cons-CD nd)) → ConsRecv (cph (SN.NodeStateD.cons-CD nd′))
             → BFcHasBlk (SN.NodeStateD.bfC-CD nd))
          -- SESSION-51 (mirror)
          → (ConsHeld (cph (SN.NodeStateD.cons-CD nd))
             → cblk (SN.NodeStateD.cons-CD nd′) ≡ cblk (SN.NodeStateD.cons-CD nd))
          -- SESSION-56 (owner grant #5, (P8)) — the mirror of the BD field
          → (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)
               ─[ ev (evl (evLabel X e a)) ]─►
               SN.decConsD linkCD (SN.NodeStateD.cons-CD nd′))
          → NodeDDrv nd e a M

-- firing link = linkBD (G1): cons-BD advances (genuine), cons-CD/bfC-CD literal
nodeD-api-BD-drv : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁BD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁BD
  → ApiHasLink linkBD e
  → NodeDDrv nd e a (B₁ ∥⇘ apiES ⇙ (D₁BD ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)))
nodeD-api-BD-drv nd {X} {e} {a} apimem bStep sDBD ahl
  with consDAdv-of⁺ linkBD (SN.NodeStateD.cons-BD nd) sDBD
... | b′ , cp′ , refl , cadv , lblv , cfix
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem (_ , sBCD))
...   | PEA.evL _ sBBD
      with absBundleG-api-evo linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) apimem sBBD
...     | bgEB⁺ csc′ css′ bfc′ bfs′ ip′ eq run evo _ =
          ndDrvBD (SN.mkNodeD csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) ip′ (SN.NodeStateD.inert-CD nd))
            (cong (λ z → (z ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) ∥⇘ apiES ⇙ (SN.decConsD linkBD (consD b′ cp′) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ahl linkBD≢linkCD apimem)) run)
               (ev→wev (⦀-ev-L (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) _ sDBD (noOffer→viewV _ (drvD-CD-no nd ahl)))))
            -- SESSION-40: the anchored classifier pins the label at `b′`, and
            -- `nd′`'s BD slot IS `consD b′ cp′`, so the successor conjunct is `refl`
            cadv refl refl (λ hcp → b′ , lblv hcp , refl ,
               bundle-recv-cliPos linkBD hi lo (λ ())
                 (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (subst (λ z → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl z) ]─► _)
                        (lblv hcp) sBBD))
            evo
            (λ hPre hRecv →
               bundle-recvBFBlock-forces-src linkBD hi lo (λ ())
                 (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
                 (subst (λ z → absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ─[ ev (evl z) ]─► _)
                        (lblv (consAdv-recv-src cadv hPre hRecv)) sBBD))
            cfix
            -- SESSION-56: the driver step, carried instead of dropped
            sDBD

-- firing link = linkCD (G2): cons-CD advances (genuine), cons-BD/bfC-BD literal
nodeD-api-CD-drv : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁CD : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
     ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decConsD linkCD (SN.NodeStateD.cons-CD nd) ─[ ev (evl (evLabel X e a)) ]─► D₁CD
  → ApiHasLink linkCD e
  → NodeDDrv nd e a (B₁ ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ D₁CD))
nodeD-api-CD-drv nd {X} {e} {a} apimem bStep sDCD ahl
  with consDAdv-of⁺ linkCD (SN.NodeStateD.cons-CD nd) sDCD
... | b′ , cp′ , refl , cadv , lblv , cfix
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
           (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBBD = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evBoth _ sBBD _ = ⊥-elim (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem (_ , sBBD))
...   | PEA.evR _ sBCD
      with absBundleG-api-evo linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) apimem sBCD
...     | bgEB⁺ csc′ css′ bfc′ bfs′ ip′ eq run evo _ =
          ndDrvCD (SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd) csc′ css′ bfc′ bfs′ (consD b′ cp′) (SN.NodeStateD.inert-BD nd) ip′)
            (cong (λ z → (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ z) ∥⇘ apiES ⇙ (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (consD b′ cp′))) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ahl (λ q → linkBD≢linkCD (sym q)) apimem)) run)
               (ev→wev (⦀-ev-R _ (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) sDCD (noOffer→viewV _ (drvD-BD-no nd ahl)))))
            -- SESSION-40 anchor (mirror of the BD site)
            cadv refl refl (λ hcp → b′ , lblv hcp , refl ,
               bundle-recv-cliPos linkCD hi lo (λ ())
                 (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (subst (λ z → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl z) ]─► _)
                        (lblv hcp) sBCD))
            evo
            (λ hPre hRecv →
               bundle-recvBFBlock-forces-src linkCD hi lo (λ ())
                 (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
                 (subst (λ z → absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) ─[ ev (evl z) ]─► _)
                        (lblv (consAdv-recv-src cadv hPre hRecv)) sBCD))
            cfix
            -- SESSION-56: the driver step, carried instead of dropped
            sDCD

-- node-D api inversion (mirror `PipeNodeFixApi.nodeD-ev-api-abs-cls`)
nodeD-ev-api-drv : (nd : SN.NodeStateD) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeD nd ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeDDrv nd e a M
nodeD-ev-api-drv nd {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
          ⦀ absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
         (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ SN.decConsD linkCD (SN.NodeStateD.cons-CD nd))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (SN.decConsD linkBD (SN.NodeStateD.cons-BD nd)) (SN.decConsD linkCD (SN.NodeStateD.cons-CD nd)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDBD = nodeD-api-BD-drv nd apimem bStep sDBD (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
... | PEA.evR _ sDCD = nodeD-api-CD-drv nd apimem bStep sDCD (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)
... | PEA.evBoth _ sDBD sDCD = ⊥-elim (linkBD≢linkCD
        (apiLink-inj (decConsD-ev-link linkBD (SN.NodeStateD.cons-BD nd) sDBD)
                     (decConsD-ev-link linkCD (SN.NodeStateD.cons-CD nd) sDCD)))

------------------------------------------------------------------------
-- node-B genuine-relay peel record: successor node, node weak run, and the
-- `RelayStepKind` of the isolated `decCP` step (via `cpStepKind-of`).  Mirror
-- of `PipeNodeFixApi.nodeB-api-*-abs-cls` with the `cpW` drop + client class
-- replaced by the `RelayStepKind`.
------------------------------------------------------------------------

data NodeBDrv (nb : SN.NodeStateB) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (M : NetProc) : Set₁ where
  nbDrv : (nb′ : SN.NodeStateB) → M ≡ absNodeB nb′
        → SN.decNodeB nb ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeB nb′
        → RelayStepKind (SN.NodeStateB.cp-B nb) (SN.NodeStateB.cp-B nb′)
        → ((SN.NodeStateB.bfC-AB nb ≡ SN.NodeStateB.bfC-AB nb′)
           ⊎ (BFcHasBlk (SN.NodeStateB.bfC-AB nb′) → ⊥))
        -- SESSION-45: PLUS the relayed block, named on both sides — the co-firing
        -- client held it and the successor phase records it
        -- TASK-3 SLICE D: the premise is the WIDENED one `PipeValRelay`'s
        -- `cpStepKindL-of⁺` now takes (`RelayPre × RelayHas`, OR the source-phase
        -- `cp3` pin); conclusion and arity unchanged, original re-derivable as
        -- `λ hPre hHas → new (inj₁ (hPre , hHas))`
        → (((RelayPre (SN.NodeStateB.cp-B nb) × RelayHas (SN.NodeStateB.cp-B nb′))
            ⊎ (Σ[ b ∈ Block₃ ] SN.NodeStateB.cp-B nb ≡ SN.consuming b SN.cp3))
           → BFcHasBlk (SN.NodeStateB.bfC-AB nb)
             × (Σ[ bc ∈ Block₃ ] (SN.NodeStateB.bfC-AB nb ≡ SN.bcBlk1 bc)
                                × (SN.NodeStateB.cp-B nb′ ≡ SN.consuming bc SN.cp4)))
        -- SESSION-33 (G2c): node B's BD BF-SERVER slot (= `dnSrv legBD`)
        → ((SN.NodeStateB.bfS-BD nb ≡ SN.NodeStateB.bfS-BD nb′)
           ⊎ ((BFsHasBlk (SN.NodeStateB.bfS-BD nb′) → ⊥)
              ⊎ RelayFwd (SN.NodeStateB.cp-B nb′)))
        -- SESSION-51: the relay's own VALUE map off the receive region …
        → ((RelayPre (SN.NodeStateB.cp-B nb) → ⊥)
           → RelayValOK (SN.NodeStateB.cp-B nb) → RelayValOK (SN.NodeStateB.cp-B nb′))
        -- … and the RAW BD-server witness (`dnSrv legBD`'s value side)
        → SrvValEvo linkBD (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.bfS-BD nb′) e a
        -- TASK-3 SLICE C (leaf 8): the relay's recorded BLOCK is fixed off the
        -- receive region — `cpStepKindL-of⁺`'s new seventh component, threaded
        -- verbatim (appended LAST, so existing destructurings gain one binder)
        → ((RelayPre (SN.NodeStateB.cp-B nb) → ⊥) → (bb : Block₃)
           → RelayAt bb (SN.NodeStateB.cp-B nb) → RelayAt bb (SN.NodeStateB.cp-B nb′))
        → NodeBDrv nb e a M

-- firing link = linkAB (consume leg, LEFT bundle)
nodeB-api-AB-drv : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
     ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAB e
  → NodeBDrv nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-AB-drv nb {X} {e} {a} apimem bStep dStep ahl
  with cpStepKindL-of⁺ linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
... | x′ , refl , rk , lblR , fwdR , rval , blkR
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem (_ , sBBD))
...   | PEA.evBoth _ _ sBBD = ⊥-elim (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem (_ , sBBD))
...   | PEA.evL _ sBAB
      with absBundleG-api-evo linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) apimem sBAB
...     | bgEB⁺ csc′ css′ bfc′ bfs′ ip′ eq run evo _ =
          nbDrv (SN.mkNodeB csc′ css′ bfc′ bfs′ (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) x′ ip′ (SN.NodeStateB.inert-BD nb))
            (cong (λ z → (z ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahl linkAB≢linkBD apimem)) run)
               (ev→wev dStep))
            rk
            evo
            (λ w →
               bundle-recvBFBlock-forces-src linkAB hi lo (λ ())
                 (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                 (subst (λ z → absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ─[ ev (evl z) ]─► _)
                        (proj₁ (proj₂ (lblR w))) sBAB)
             -- SESSION-45: the same pinned step also names the client's block,
             -- and `cpStepKindL-of⁺` names the successor phase at that block
             , proj₁ (lblR w)
             , bundle-recv-cliPos linkAB hi lo (λ ())
                 (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
                 (subst (λ z → absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ─[ ev (evl z) ]─► _)
                        (proj₁ (proj₂ (lblR w))) sBAB)
             , proj₂ (proj₂ (lblR w)))
            (inj₁ refl)
            rval (inj₁ refl) blkR

-- firing link = linkBD (produce leg, RIGHT bundle)
nodeB-api-BD-drv : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
     ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkBD e
  → NodeBDrv nb e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeB-api-BD-drv nb {X} {e} {a} apimem bStep dStep ahl
  with cpStepKindL-of⁺ linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
... | x′ , refl , rk , lblR , fwdR , rval , blkR
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
           (absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAB = ⊥-elim (absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB))
...   | PEA.evBoth _ sBAB _ = ⊥-elim (absBundleG-api-no linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem (_ , sBAB))
...   | PEA.evR _ sBBD
      with absBundleG-api-evo linkBD lo hi (λ ()) (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) apimem sBBD
...     | bgEB⁺ csc′ css′ bfc′ bfs′ ip′ eq run _ srvEvo =
          nbDrv (SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) csc′ css′ bfc′ bfs′ x′ (SN.NodeStateB.inert-AB nb) ip′)
            (cong (λ z → (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAB linkBD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ahl (λ q → linkAB≢linkBD (sym q)) apimem)) run)
               (ev→wev dStep))
            rk
            (inj₁ refl)
            (λ w → ⊥-elim
               (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ahlBF linkAB≢linkBD tt
                 (_ , subst (λ z → absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) ─[ ev (evl z) ]─► _)
                        (proj₁ (proj₂ (lblR w))) sBBD)))
            (srvEvo⇒fwd (SN.NodeStateB.bfS-BD nb) bfs′ x′ fwdR srvEvo)
            rval srvEvo blkR

-- node-B api inversion
nodeB-ev-api-drv : (nb : SN.NodeStateB) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeB nb ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeBDrv nb e a M
nodeB-ev-api-drv nb {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)
          ⦀ absBundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
         (SN.decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAB linkBD (SN.NodeStateB.cp-B nb) dStep
... | inj₁ ahl = nodeB-api-AB-drv nb apimem bStep dStep ahl
... | inj₂ ahl = nodeB-api-BD-drv nb apimem bStep dStep ahl

------------------------------------------------------------------------
-- node-C genuine-relay peel record (symmetric to node B: links AC / CD).
------------------------------------------------------------------------

data NodeCDrv (nc : SN.NodeStateC) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (M : NetProc) : Set₁ where
  ncDrv : (nc′ : SN.NodeStateC) → M ≡ absNodeC nc′
        → SN.decNodeC nc ═[ ev (evl (evLabel X e a)) ]═► SN.decNodeC nc′
        → RelayStepKind (SN.NodeStateC.cp-C nc) (SN.NodeStateC.cp-C nc′)
        → ((SN.NodeStateC.bfC-AC nc ≡ SN.NodeStateC.bfC-AC nc′)
           ⊎ (BFcHasBlk (SN.NodeStateC.bfC-AC nc′) → ⊥))
        -- SESSION-45 (mirror)
        -- TASK-3 SLICE D (mirror): the WIDENED premise
        → (((RelayPre (SN.NodeStateC.cp-C nc) × RelayHas (SN.NodeStateC.cp-C nc′))
            ⊎ (Σ[ b ∈ Block₃ ] SN.NodeStateC.cp-C nc ≡ SN.consuming b SN.cp3))
           → BFcHasBlk (SN.NodeStateC.bfC-AC nc)
             × (Σ[ bc ∈ Block₃ ] (SN.NodeStateC.bfC-AC nc ≡ SN.bcBlk1 bc)
                                × (SN.NodeStateC.cp-C nc′ ≡ SN.consuming bc SN.cp4)))
        -- SESSION-33 (G2c): node C's CD BF-SERVER slot (= `dnSrv legCD`)
        → ((SN.NodeStateC.bfS-CD nc ≡ SN.NodeStateC.bfS-CD nc′)
           ⊎ ((BFsHasBlk (SN.NodeStateC.bfS-CD nc′) → ⊥)
              ⊎ RelayFwd (SN.NodeStateC.cp-C nc′)))
        -- SESSION-51 (mirror of node B)
        → ((RelayPre (SN.NodeStateC.cp-C nc) → ⊥)
           → RelayValOK (SN.NodeStateC.cp-C nc) → RelayValOK (SN.NodeStateC.cp-C nc′))
        → SrvValEvo linkCD (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.bfS-CD nc′) e a
        -- TASK-3 SLICE C (leaf 8), mirror of node B
        → ((RelayPre (SN.NodeStateC.cp-C nc) → ⊥) → (bb : Block₃)
           → RelayAt bb (SN.NodeStateC.cp-C nc) → RelayAt bb (SN.NodeStateC.cp-C nc′))
        → NodeCDrv nc e a M

-- firing link = linkAC (consume leg, LEFT bundle)
nodeC-api-AC-drv : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
     ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkAC e
  → NodeCDrv nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-AC-drv nc {X} {e} {a} apimem bStep dStep ahl
  with cpStepKindL-of⁺ linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
... | x′ , refl , rk , lblR , fwdR , rval , blkR
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) bStep
...   | PEA.evSync () _ _
...   | PEA.evR _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem (_ , sBCD))
...   | PEA.evBoth _ _ sBCD = ⊥-elim (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem (_ , sBCD))
...   | PEA.evL _ sBAC
      with absBundleG-api-evo linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) apimem sBAC
...     | bgEB⁺ csc′ css′ bfc′ bfs′ ip′ eq run evo _ =
          ncDrv (SN.mkNodeC csc′ css′ bfc′ bfs′ (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) x′ ip′ (SN.NodeStateC.inert-CD nc))
            (cong (λ z → (z ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-L _ _ (noOffer→viewV _ (bundleG-api-no linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahl linkAC≢linkCD apimem)) run)
               (ev→wev dStep))
            rk
            evo
            (λ w →
               bundle-recvBFBlock-forces-src linkAC hi lo (λ ())
                 (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                 (subst (λ z → absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ─[ ev (evl z) ]─► _)
                        (proj₁ (proj₂ (lblR w))) sBAC)
             -- SESSION-45: the same pinned step also names the client's block,
             -- and `cpStepKindL-of⁺` names the successor phase at that block
             , proj₁ (lblR w)
             , bundle-recv-cliPos linkAC hi lo (λ ())
                 (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
                 (subst (λ z → absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ─[ ev (evl z) ]─► _)
                        (proj₁ (proj₂ (lblR w))) sBAC)
             , proj₂ (proj₂ (lblR w)))
            (inj₁ refl)
            rval (inj₁ refl) blkR

-- firing link = linkCD (produce leg, RIGHT bundle)
nodeC-api-CD-drv : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {B₁ D₁ : NetProc}
  → apiES .mem (X , e) a
  → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
     ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc) ─[ ev (evl (evLabel X e a)) ]─► D₁
  → ApiHasLink linkCD e
  → NodeCDrv nc e a (B₁ ∥⇘ apiES ⇙ D₁)
nodeC-api-CD-drv nc {X} {e} {a} apimem bStep dStep ahl
  with cpStepKindL-of⁺ linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
... | x′ , refl , rk , lblR , fwdR , rval , blkR
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
           (absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)) bStep
...   | PEA.evSync () _ _
...   | PEA.evL _ sBAC = ⊥-elim (absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC))
...   | PEA.evBoth _ sBAC _ = ⊥-elim (absBundleG-api-no linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem (_ , sBAC))
...   | PEA.evR _ sBCD
      with absBundleG-api-evo linkCD lo hi (λ ()) (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) apimem sBCD
...     | bgEB⁺ csc′ css′ bfc′ bfs′ ip′ eq run _ srvEvo =
          ncDrv (SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) csc′ css′ bfc′ bfs′ x′ (SN.NodeStateC.inert-AC nc) ip′)
            (cong (λ z → (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ z) ∥⇘ apiES ⇙ SN.decCP linkAC linkCD x′) eq)
            (∥⇘⇙-wev-sync apiES _ _ apimem
               (⦀-wev-R _ _ (noOffer→viewV _ (bundleG-api-no linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ahl (λ q → linkAC≢linkCD (sym q)) apimem)) run)
               (ev→wev dStep))
            rk
            (inj₁ refl)
            (λ w → ⊥-elim
               (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ahlBF linkAC≢linkCD tt
                 (_ , subst (λ z → absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) ─[ ev (evl z) ]─► _)
                        (proj₁ (proj₂ (lblR w))) sBCD)))
            (srvEvo⇒fwd (SN.NodeStateC.bfS-CD nc) bfs′ x′ fwdR srvEvo)
            rval srvEvo blkR

-- node-C api inversion
nodeC-ev-api-drv : (nc : SN.NodeStateC) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodeC nc ─[ ev (evl (evLabel X e a)) ]─► M
  → NodeCDrv nc e a M
nodeC-ev-api-drv nc {X} {e} {a} apimem step
  with SStep.reflect-node-api
         (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)
          ⦀ absBundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
         (SN.decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
         apimem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with decCP-ev-link linkAC linkCD (SN.NodeStateC.cp-C nc) dStep
... | inj₁ ahl = nodeC-api-AC-drv nc apimem bStep dStep ahl
... | inj₂ ahl = nodeC-api-CD-drv nc apimem bStep dStep ahl

------------------------------------------------------------------------
-- `LegDriverStep l s s′ e a`: for delivery leg `l`, HOW leg `l`'s three drivers
-- relate across the visible step — either the ONE firing driver's genuine
-- advance (carrying exactly the ambient component FIXITIES the matching
-- `PipeEvDriver.pres-*` consumes) or leg-wide FIXITY (the event fired on the
-- OTHER leg / node A's other producer).
------------------------------------------------------------------------

data LegDriverStep (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
                   (e : Net_Api Payload X) (a : X) : Set₁ where
  -- node A fired leg `l`'s producer: genuine `ProdAdv`, rest fixed
  ldProd  : ProdAdv (prodOf l s) (prodOf l s′)
          → relayOf  l s ≡ relayOf  l s′ → phOf     l s ≡ phOf     l s′
          → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
          → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
          → LegDriverStep l s s′ e a
  -- node B/C fired leg `l`'s relay: the isolated `decCP` `RelayStepKind`, with
  -- prod / D-consume / both cells / downstream client fixed.  The relay's OWN
  -- upstream client may move — its EVOLUTION disjunct (fixed, or fired-visibly
  -- ⇒ ¬-block successor) and the receive-coupling `wUp` fact are carried
  -- (session-26 cone-witness extension) exactly as `pres-relay` demands them.
  ldRelay : RelayStepKind (relayOf l s) (relayOf l s′)
          → prodOf   l s ≡ prodOf   l s′ → phOf     l s ≡ phOf     l s′
          → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
          → dnClient l s ≡ dnClient l s′
          → ((upClient l s ≡ upClient l s′) ⊎ (BFcHasBlk (upClient l s′) → ⊥))
          -- SESSION-45: PLUS the relayed block, so `PipeVal` clause (3) can hand
          -- clause (4) its value
          -- TASK-3 SLICE D: the WIDENED premise (see `NodeBDrv`)
          → (((RelayPre (relayOf l s) × RelayHas (relayOf l s′))
              ⊎ (Σ[ b ∈ Block₃ ] relayOf l s ≡ SN.consuming b SN.cp3))
             → BFcHasBlk (upClient l s)
               × (Σ[ bc ∈ Block₃ ] (upClient l s ≡ SN.bcBlk1 bc)
                                  × (relayOf l s′ ≡ SN.consuming bc SN.cp4)))
          -- TASK-3 SLICE C (leaf 8): PLUS the relay's recorded-BLOCK fixity off
          -- the receive region.  `RelayStepKind` is phase-only and cannot carry
          -- it, so it rides beside, exactly as `wUp` does; appended LAST so the
          -- four existing destructurings gain one binder and nothing else.
          → ((RelayPre (relayOf l s) → ⊥) → (bb : Block₃)
             → RelayAt bb (relayOf l s) → RelayAt bb (relayOf l s′))
          → LegDriverStep l s s′ e a
  -- node D fired leg `l`'s consumer: genuine `ConsAdv` + the `cp3 → recvBFBlock`
  -- label witness, with prod / relay / both cells / upstream client fixed.  The
  -- consumer's OWN downstream client may move — its EVOLUTION disjunct and the
  -- receive-coupling `wDn` fact are carried exactly as `pres-cons` demands them.
  ldCons  : ConsAdv (phOf l s) (phOf l s′)
          -- SESSION-40 ANCHOR: and `b″` is the block the SUCCESSOR slot records
          → (phOf l s ≡ cp3
             → Σ[ b″ ∈ Block₃ ]
                 (evLabel X e a ≡ evLabel Block₃ (apiBF (linkOf l) hi recvBFBlock) b″)
               × (cblkOf l s′ ≡ b″)
               -- SESSION-41: and the CO-FIRING client held exactly that block,
               -- so `PipeVal` clause (7) hands clause (8) its value
               × (dnClient l s ≡ SN.bcBlk1 b″))
          → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
          → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
          → upClient l s ≡ upClient l s′
          → ((dnClient l s ≡ dnClient l s′) ⊎ (BFcHasBlk (dnClient l s′) → ⊥))
          → (InCp03 (phOf l s) → ConsRecv (phOf l s′) → BFcHasBlk (dnClient l s))
          → LegDriverStep l s s′ e a
  -- the event fired elsewhere: leg `l` is entirely fixed
  ldFix   : prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
          → phOf     l s ≡ phOf     l s′
          → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
          → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
          → LegDriverStep l s s′ e a

------------------------------------------------------------------------
-- SESSION-51: `LegValStep l s s′ e a` — the four VALUE facts `LegDriverStep`
-- does NOT carry, which `PipeValInv.PipeVal`'s clauses (1)/(4)/(5)/(8) need.
-- Appended BESIDE `LegDriverStep` (never inside it) so `PipeEvStep`'s
-- `legStep→pres`/`legStep→pmono`/`legStep→rmono` are untouched.
--
--   · the two BF-SERVER slots' RAW witnesses — `UpSrvEvo`/`DnSrvEvo` project the
--     fired block away, so `SrvValOK (upSrv l s′)` is unreachable from them;
--   · the relay driver's value map OFF the receive region (on it the value comes
--     from the co-firing BF client, via `ldRelay`'s `wUp`);
--   · node D's recorded-block FIXITY past the receive (on the `cp3` hop the value
--     comes from `ldCons`'s anchor).
------------------------------------------------------------------------

record LegValStep (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
                  (e : Net_Api Payload X) (a : X) : Set₁ where
  constructor lvStep
  field
    lvUpSrv : SrvValEvo (upLinkOf l) (upSrv l s) (upSrv l s′) e a
    lvDnSrv : SrvValEvo (linkOf   l) (dnSrv l s) (dnSrv l s′) e a
    lvRelay : (RelayPre (relayOf l s) → ⊥)
            → RelayValOK (relayOf l s) → RelayValOK (relayOf l s′)
    lvCons  : ConsHeld (phOf l s) → cblkOf l s′ ≡ cblkOf l s
open LegValStep public

------------------------------------------------------------------------
-- `driverExpose`: the whole-nodes dispatch (re-mirror of
-- `PipeNodeFixApi.top-nodes-abs-expose-cls`, node A REUSED, B/C/D via the
-- genuine `-drv` peels above) returning, for BOTH legs, the `LegDriverStep`.
------------------------------------------------------------------------

driverExpose : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → SStep.absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ SStep.absNodesOf s′)
      × (SStep.nodesOf s ═[ ev (evl (evLabel X e a)) ]═► SStep.nodesOf s′)
      × LegDriverStep legBD s s′ e a × LegDriverStep legCD s s′ e a
      -- SESSION-33 (G2c): the two BF-SERVER slots of EACH leg, in the shape
      -- `PipeSrvInv.srvCoupled-pres` consumes (do NOT extend `LegDriverStep`
      -- — that would disturb `PipeEvStep.legStep→pres`)
      × (UpSrvEvo legBD s s′ × DnSrvEvo legBD s s′)
      × (UpSrvEvo legCD s s′ × DnSrvEvo legCD s s′)
      -- SESSION-51: the two legs' VALUE step data (appended at the END, so the
      -- single destructuring site in `PipeEvStep` gains only new binders)
      × LegValStep legBD s s′ e a × LegValStep legCD s s′ e a
driverExpose s apimem nodesStep
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (absNodeA (nA s)) (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))) nodesStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sA sRest = ⊥-elim (SStep.⦀-noOffer (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s))
        (absNodeB-no-when-A (nB s) apimem (absNodeA-fp (nA s) apimem sA))
        (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
          (absNodeC-no-when-A (nC s) apimem (absNodeA-fp (nA s) apimem sA))
          (absNodeD-no-when-A (nD s) apimem (absNodeA-fp (nA s) apimem sA))) (_ , sRest))
... | PEA.evL _ sA with nodeA-ev-api-abs-evo (nA s) apimem sA
...   | naEBaev1 na′ Meq weakRunA padv pACeq srvAB sACeq =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        wrunA ,
        ldProd padv refl refl refl refl refl refl ,
        ldFix (sym pACeq) refl refl refl refl refl refl ,
        (proj₁ srvAB , inj₁ refl) , (inj₁ sACeq , inj₁ refl) ,
        lvStep (proj₂ srvAB) (inj₁ refl) (λ _ h → h) (λ _ → refl) ,
        lvStep (inj₁ sACeq)  (inj₁ refl) (λ _ h → h) (λ _ → refl)
  where
    fpA = absNodeA-fp (nA s) apimem sA
    wrunA = ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (nodeB-no-when-A (nB s) apimem fpA)
                 (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (nodeC-no-when-A (nC s) apimem fpA) (nodeD-no-when-A (nD s) apimem fpA))))
              weakRunA
...   | naEBaev2 na′ Meq weakRunA padv pABeq srvAC sABeq =
        mkSys (med s) na′ (nB s) (nC s) (nD s) , refl ,
        cong (λ z → z ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        wrunA ,
        ldFix (sym pABeq) refl refl refl refl refl refl ,
        ldProd padv refl refl refl refl refl refl ,
        (inj₁ sABeq , inj₁ refl) , (proj₁ srvAC , inj₁ refl) ,
        lvStep (inj₁ sABeq)  (inj₁ refl) (λ _ h → h) (λ _ → refl) ,
        lvStep (proj₂ srvAC) (inj₁ refl) (λ _ h → h) (λ _ → refl)
  where
    fpA = absNodeA-fp (nA s) apimem sA
    wrunA = ⦀-wev-L (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (nodeB-no-when-A (nB s) apimem fpA)
                 (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (nodeC-no-when-A (nC s) apimem fpA) (nodeD-no-when-A (nD s) apimem fpA))))
              weakRunA
driverExpose s apimem nodesStep | PEA.evR _ sRest
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (absNodeB (nB s)) (absNodeC (nC s) ⦀ absNodeD (nD s)) sRest
... | PEA.evSync () _ _
... | PEA.evBoth _ sB sCD = ⊥-elim (SStep.⦀-noOffer (absNodeC (nC s)) (absNodeD (nD s))
        (absNodeC-no-when-B (nC s) apimem (absNodeB-fp (nB s) apimem sB))
        (absNodeD-no-when-B (nD s) apimem (absNodeB-fp (nB s) apimem sB)) (_ , sCD))
... | PEA.evL _ sB with nodeB-ev-api-drv (nB s) apimem sB
...   | nbDrv nb′ Meq weakRunB rk upEvo wUp srvBD rvalB srvBDraw blkRB =
        mkSys (med s) (nA s) nb′ (nC s) (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (z ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-no-when-B (nA s) apimem fpB))
          (⦀-wev-L (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (SStep.⦀-noOffer (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (nodeC-no-when-B (nC s) apimem fpB) (nodeD-no-when-B (nD s) apimem fpB)))
             weakRunB)
        ,
        ldRelay rk refl refl refl refl refl upEvo wUp blkRB ,
        ldFix refl refl refl refl refl refl refl ,
        (inj₁ refl , srvBD) , (inj₁ refl , inj₁ refl) ,
        lvStep (inj₁ refl) srvBDraw   rvalB       (λ _ → refl) ,
        lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) (λ _ → refl)
  where fpB = absNodeB-fp (nB s) apimem sB
driverExpose s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) sCD
... | PEA.evSync () _ _
... | PEA.evBoth _ sC sD = ⊥-elim (absNodeD-no-when-C (nD s) apimem (absNodeC-fp (nC s) apimem sC) (_ , sD))
... | PEA.evL _ sC with nodeC-ev-api-drv (nC s) apimem sC
...   | ncDrv nc′ Meq weakRunC rk upEvo wUp srvCD rvalC srvCDraw blkRC =
        mkSys (med s) (nA s) (nB s) nc′ (nD s) , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (z ⦀ absNodeD (nD s)))) Meq ,
        ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
          (noOffer→viewV _ (nodeA-no-when-C (nA s) apimem fpC))
          (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
             (noOffer→viewV _ (nodeB-no-when-C (nB s) apimem fpC))
             (⦀-wev-L (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                (noOffer→viewV _ (nodeD-no-when-C (nD s) apimem fpC))
                weakRunC))
        ,
        ldFix refl refl refl refl refl refl refl ,
        ldRelay rk refl refl refl refl refl upEvo wUp blkRC ,
        (inj₁ refl , inj₁ refl) , (inj₁ refl , srvCD) ,
        lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) (λ _ → refl) ,
        lvStep (inj₁ refl) srvCDraw   rvalC       (λ _ → refl)
  where fpC = absNodeC-fp (nC s) apimem sC
driverExpose s apimem nodesStep | PEA.evR _ sRest | PEA.evR _ sCD | PEA.evR _ sD
    with nodeD-ev-api-drv (nD s) apimem sD
... | ndDrvBD nd′ Meq weakRunD cadv cCDeq bfcCDeq lblD dnEvo wDn cfixD drvD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        wrunD ,
        ldCons cadv lblD refl refl refl refl refl dnEvo wDn ,
        ldFix refl refl (cong cph (sym cCDeq)) refl refl refl (sym bfcCDeq) ,
        (inj₁ refl , inj₁ refl) , (inj₁ refl , inj₁ refl) ,
        lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) cfixD ,
        lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) (λ _ → cong cblk cCDeq)
  where
    fpD = absNodeD-fp (nD s) apimem sD
    wrunD = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem fpD))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem fpD))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem fpD))
                    weakRunD))
... | ndDrvCD nd′ Meq weakRunD cadv cBDeq bfcBDeq lblD dnEvo wDn cfixD drvD =
        mkSys (med s) (nA s) (nB s) (nC s) nd′ , refl ,
        cong (λ z → absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ z))) Meq ,
        wrunD ,
        ldFix refl refl (cong cph (sym cBDeq)) refl refl refl (sym bfcBDeq) ,
        ldCons cadv lblD refl refl refl refl refl dnEvo wDn ,
        (inj₁ refl , inj₁ refl) , (inj₁ refl , inj₁ refl) ,
        lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) (λ _ → cong cblk cBDeq) ,
        lvStep (inj₁ refl) (inj₁ refl) (λ _ h → h) cfixD
  where
    fpD = absNodeD-fp (nD s) apimem sD
    wrunD = ⦀-wev-R (SN.decNodeA (nA s)) (SN.decNodeB (nB s) ⦀ (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s)))
              (noOffer→viewV _ (nodeA-no-when-D (nA s) apimem fpD))
              (⦀-wev-R (SN.decNodeB (nB s)) (SN.decNodeC (nC s) ⦀ SN.decNodeD (nD s))
                 (noOffer→viewV _ (nodeB-no-when-D (nB s) apimem fpD))
                 (⦀-wev-R (SN.decNodeC (nC s)) (SN.decNodeD (nD s))
                    (noOffer→viewV _ (nodeC-no-when-D (nC s) apimem fpD))
                    weakRunD))

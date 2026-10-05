{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- InFlightOpen completion, Task 3 — THE api FAMILY: the two RELAY-DRIVER
-- positions `InFlightOpen.oRelayIn` / `oRelayOut`, at both legs.
--
-- WHAT A RELAY-DRIVER POSITION IS, and why it is the LAST family.  `AtPos l
-- lpRelayIn b s` pins the relay driver to `consuming _ cp4..cp6` and `AtPos l
-- lpRelayOut b s` to `producing _ pp0..pp5` (`LiveLegInv.RelayIn`/`RelayOut`,
-- `:157-180`), i.e. NINE sub-phases across the two positions.  At every one of
-- them the driver offers exactly ONE api event, and — unlike the io families —
-- that event is in `apiES`, so it SYNCS with the relay node's own CS/BF peer.
-- The nine (event, co-party) pairs, re-derived from `SysNode.decCons`
-- (`:951-958`) and `decProd` (`:806-830`) and `FourNodeDiamond.produce`:
--
--   sub-phase   driver's api event                     co-party peer slot
--   ---------   ------------------------------------   ---------------------
--   cp4         `apiBF up hi sendBFClientDone ! tt`    up BF client  @ bcIdle
--   cp5         `apiCS up hi sendCSDone`               up CS client  @ ccIdle
--   cp6 / pp0   `apiCS dn hi reqCSRequestNext`         dn CS server  @ csAreq
--   pp1         `apiCS dn hi sendCSAwaitReply`         dn CS server  @ csCanAwait
--   pp2         `apiCS dn hi sendCSRollForward ! ht`   dn CS server  @ csMust
--   pp3         `apiBF dn hi reqBFRange`               dn BF server  @ bsAreq r
--   pp4         `apiBF dn hi sendBFStartBatch ! tt`    dn BF server  @ bsBusy
--   pp5         `apiBF dn hi sendBFBlock ! b`          dn BF server  @ bsStream
--
-- (`cp6` and `pp0` coincide: `decCP l₁ l₂ (consuming b cp6)` is
-- `Ret b >>= λ b′ → produce l₂ hi b′`, and `force (P >>= k)` at a `ret` IS
-- `force (k r)` with NO intervening `sil` (`CSP/Operators.agda:338`), so the
-- `cp6` tree is DEFINITIONALLY the `pp0` tree — §4's `relay-offer-cp6` is
-- literally `relay-offer-pp0`.  The LegPos-24 spike's "`cp6` is a free τ"
-- reading is refuted by that same equation.)
--
-- *** WHAT THIS MODULE DELIVERS, AND WHAT IT DOES NOT — READ THIS BEFORE
-- QUOTING §7. ***  It delivers, as THEOREMS:
--
--   (1) the whole api LADDER, invariant-free and generic in the link, the
--       direction and the carried value: nine peer offers (§2), nine driver
--       offers (§3), and the four per-leg SYNC KITS that turn "co-party offers
--       it AND driver offers it" into `⊥` from `isStable` (§4);
--   (2) the NINE per-sub-phase ARM THEOREMS (§5) — each takes ONE co-position
--       equation on the co-party slot named in the table above and nothing else
--       (no `broken`, no `ChanUp`/`ChanDn`, no `NoTwoTokens`: an api sync needs
--       no medium operand at all, which is why the api family's ladder is
--       cheaper than the io family's and its INVARIANT content dearer);
--   (3) the two TOTAL dispatches on `CPPh` (§6) reducing `RefutedAt l lpRelayIn`
--       / `lpRelayOut` to exactly those nine obligations, packaged as the ONE
--       predicate `RelayCo` (`CoAt` at the driver's actual phase — the two
--       positions pin DISJOINT regions of `CPPh`, so one dispatch serves both),
--       plus the four facts, their window corollaries, and — §6e, the shape a
--       consumer must use — their `isStable`-SCOPED forms.
--
-- It does NOT discharge `RelayCo`.  That predicate is the residual, and §7
-- records — with the machine-checkable reasons — WHY it is not dischargeable
-- from anything the campaign carries, and what it costs.
--
-- *** THE RESIDUAL IS SCOPED BY `isStable`, AND THAT IS NOT COSMETIC. ***  As a
-- BARE state predicate `RelayCo` is FALSE at reachable states (§7(a) gives the
-- counter-state), so a premise of the form `(l) (r) → RelayCo l (toSys r)` would
-- be REFUTABLE and would make the campaign's headline theorem vacuously true —
-- strictly worse than conditional.  The consumer needs it only where
-- `RefutedAt` is asked, and `RefutedAt` HANDS THE PROOF `isStable`; so the shape
-- to thread is §6e's `isStable (radec r ∖ hidden blkA) → RelayCo l (toSys r)`,
-- which is the LegPos-24 verify report's Claim 2(b) applied at the residual
-- level as well as at the arm level.
--
-- In one line, what is missing: five of the nine sub-phases name a CHAINSYNC
-- peer position, and NO PROVED INVARIANT in this development constrains a
-- ChainSync position — the only per-state predicates that do are this module's
-- own `CoAt` and the untracked LegPos-24 spike's `SpikeAtPos`, which is
-- invariant-SHAPED but never established (no base, no step, no reachability).
-- So the api family needs a ChainSync analogue of `LiveChanInv` before its
-- dispatch can be closed.  This module therefore leaves the campaign at EIGHT of
-- twelve facts, with the remaining four reduced from two opaque "nothing is
-- offered" premises to NINE CONCRETE STATE EQUATIONS under one `isStable`.
-- *** READ THAT NINE AS OF THIS MODULE. ***  It is what this module left, and it is
-- historical: the cross-node api campaign discharged `pp4` (T1) and `pp5` (T2) off
-- `LiveDrvBF`, so the residual is SEVEN from T2 onwards (`LiveRelayCS` §2).
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `funext`, and no
-- `with` in anything whose type mentions an imported `blkA`-parameterised
-- predicate — every dispatch (the leg, and the driver's nine sub-phases) is on
-- an EXPLICIT argument, the campaign's `blkA`-module rule.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
-- the NON-polymorphic `⊤`, qualified: it is the carrier of the payload-free api
-- tags, and must not shadow the polymorphic one above
import Data.Unit as U
open import Data.Bool using ( false )
open import Data.Maybe using ( just )
open import Data.Empty using ( ⊥ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; subst )
open import Class.DecEq using ( DecEq; _≟_ )
open import Class.DecEq.Instances using ( DecEq-Fin )

open import Process_Trees using ( PTree; ExtI; isStable )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveRelayOpen
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD; produce )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; apiCS; apiBF
        ; sendCSDone; reqCSRequestNext; sendCSAwaitReply; sendCSRollForward
        ; sendBFClientDone; reqBFRange; sendBFStartBatch; sendBFBlock )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; Header; Tip; header; tip; ChainRange
        ; DecEq-ChainRange; DecEq-Header; DecEq-Tip )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( decBlock )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Examples.Cardano_network.ChainSync p as CS

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∖_; viewV; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( ev; evl; evLabel; _─[_]─►_; sVis )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; nB; nC )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( CPPh; consuming; producing
              ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              ; ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
              ; decCons; decProd; decCP )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; IoOffers; ⦀-ev-L; ⦀-ev-R; lift-api-node-ev
                 ; absCSc; absCSs; absBFc; absBFs; absBundleG; absNodeB; absNodeC
                 ; coarsenCSc; coarsenCSs; coarsenBFc; coarsenBFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( ApiHasLink; ahlCS; ahlBF; IsApiCSBF; aicCS; aicBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  using ( aCSc; aCSs; aBFc; aBFs
        ; ceqCSc03; ceqCSs06; ceqCSs07; ceqCSs11
        ; ceqBFc02; ceqBFs03; ceqBFs05; ceqBFs07 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( ≟-yes-refl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteKaTs blkA
  using ( absBundle-CSc-ev; absBundle-CSs-ev; absBundle-BFc-ev; absBundle-BFs-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA
  using ( ApiIsCons; ApiIsProd; aicCSdone; aicBFdone
        ; aipCSreq; aipCSawait; aipCSroll; aipBFreq; aipBFstart; aipBFblock )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( linkAB≢linkBD; linkAC≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( absBundleG-api-no )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( relayOf; upClient )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( relayBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( hidden )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( lpRelayIn; lpRelayOut; RelayIn; RelayOut )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer blkA
  using ( RefutedAt; Window; hiddenMove-⊥; apiNodes-whole
        ; nodes-offer-B; nodes-offer-C )

import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) as TLB

------------------------------------------------------------------------
-- §1  THE TWO MISSING ACCESSORS, AND TWO LINK DISTINCTIONS.
--
-- PRODUCER-SITE CHECK, done by grep before writing: `upClient`/`dnClient` come
-- from `PipeInv`, `upSrv`/`dnSrv` from `PipeSrvInv`, `upLink`/`dnLink` from
-- `PipeFillSource` — but NO tracked module defines the leg's two CHAINSYNC
-- slots (`grep -rn 'upCSc\|dnCSs' Liveness/` finds them only in the untracked
-- LegPos-24 spike).  They are therefore defined here, in the same shape as
-- their BlockFetch siblings.
------------------------------------------------------------------------

-- the leg's UP-hop ChainSync CLIENT: the relay node's own CS client on the leg's
-- up link, at direction `hi` (node B's AB slot / node C's AC slot)
upCSc : TwoLegs → SysState → SN.CScPos
upCSc legBD s = SN.NodeStateB.csC-AB (nB s)
upCSc legCD s = SN.NodeStateC.csC-AC (nC s)

-- … and the leg's DOWN-hop ChainSync SERVER: the relay node's CS server on the
-- leg's down link, at direction `hi` (node B's BD slot / node C's CD slot)
dnCSs : TwoLegs → SysState → SN.CSsPos
dnCSs legBD s = SN.NodeStateB.csS-BD (nB s)
dnCSs legCD s = SN.NodeStateC.csS-CD (nC s)

-- the down link differs from the up link (the flipped `SysIoLink` pair — a
-- relay node's two bundles are keyed on distinct links, which is what
-- `absBundleG-api-no` needs when the DOWN bundle is the firing one)
linkBD≢linkAB : ¬ (linkBD ≡ linkAB)
linkBD≢linkAB q = linkAB≢linkBD (sym q)

-- … the AC/CD mirror
linkCD≢linkAC : ¬ (linkCD ≡ linkAC)
linkCD≢linkAC q = linkAC≢linkCD (sym q)

------------------------------------------------------------------------
-- §2  THE NINE PEER OFFERS — each an ABSTRACT PEER STEP off ONE coarse-position
-- equation.
--
-- Every clause has the same three parts: the `abs*` peer step packager
-- (`aCSc`/`aCSs`/`aBFc`/`aBFs`, `SysOracle_PeerEvCSBF.agda:316`/`:639`/`:1018`/
-- `:1185`), the row's own `coarsen ∘ nxt` commutation (`ceq*`), and two `subst`s
-- retargeting both along the caller's pin — the shape the LegPos-24 spike's
-- `bfc-offer-cdone` established, which works because `abs*Ξ q` depends on `q`
-- only through `coarsen* q`.
--
-- NOTE what the pin buys and what it does not: it makes the peer OFFER the
-- driver's event.  It says nothing about reachability, and §7 is about exactly
-- that.
------------------------------------------------------------------------

-- (cp4)  the up BF CLIENT at a position coarsening to `bcIdle` offers the
-- relay's `sendBFClientDone` (`bfCnxt bcIdle`, `NodeSpecs.agda:521-523`)
peer-cp4 : (i : Link) (d : Dir) (q : SN.BFcPos)
         → coarsenBFc q ≡ NS.bcIdle
         → absBFc i d q ─[ ev (evl (evLabel U.⊤ (apiBF i d sendBFClientDone) U.tt)) ]─►
           absBFc i d SN.bcDone1
peer-cp4 i d q pin =
  aBFc i d q SN.bcDone1
    (subst (λ z → NS.bfCfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfCnxt i d z (U.⊤ , apiBF i d sendBFClientDone) U.tt
                  ≡ just NS.bcWcd)
           (sym pin) (ceqBFc02 i d))

-- (cp5)  the up CS CLIENT at a position coarsening to `ccIdle` offers the
-- relay's `sendCSDone` (`csCnxt ccIdle`, `NodeSpecs.agda:313-315`)
peer-cp5 : (i : Link) (d : Dir) (q : SN.CScPos)
         → coarsenCSc q ≡ NS.ccIdle
         → absCSc i d q ─[ ev (evl (evLabel U.⊤ (apiCS i d sendCSDone) U.tt)) ]─►
           absCSc i d SN.csDone1
peer-cp5 i d q pin =
  aCSc i d q SN.csDone1
    (subst (λ z → NS.csCfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csCnxt i d z (U.⊤ , apiCS i d sendCSDone) U.tt
                  ≡ just NS.ccWdone)
           (sym pin) (ceqCSc03 i d))

-- (cp6 / pp0)  the down CS SERVER at a position coarsening to `csAreq` offers
-- the relay-produce's `reqCSRequestNext` (`csSnxt csAreq`, `NodeSpecs.agda:428`)
peer-pp0 : (i : Link) (d : Dir) (q : SN.CSsPos)
         → coarsenCSs q ≡ NS.csAreq
         → absCSs i d q ─[ ev (evl (evLabel U.⊤ (apiCS i d reqCSRequestNext) U.tt)) ]─►
           absCSs i d (SN.ssHead CS.stCanAwait)
peer-pp0 i d q pin =
  aCSs i d q (SN.ssHead CS.stCanAwait)
    (subst (λ z → NS.csSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csSnxt i d z (U.⊤ , apiCS i d reqCSRequestNext) U.tt
                  ≡ just NS.csCanAwait)
           (sym pin) (ceqCSs11 i d))

-- (pp1)  … at `csCanAwait` it offers `sendCSAwaitReply` (`csSnxt csCanAwait`,
-- `NodeSpecs.agda:445`)
peer-pp1 : (i : Link) (d : Dir) (q : SN.CSsPos)
         → coarsenCSs q ≡ NS.csCanAwait
         → absCSs i d q ─[ ev (evl (evLabel U.⊤ (apiCS i d sendCSAwaitReply) U.tt)) ]─►
           absCSs i d SN.ssAw1
peer-pp1 i d q pin =
  aCSs i d q SN.ssAw1
    (subst (λ z → NS.csSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csSnxt i d z (U.⊤ , apiCS i d sendCSAwaitReply) U.tt
                  ≡ just NS.csWar)
           (sym pin) (ceqCSs06 i d))

-- (pp2)  … and at `csMust` it offers `sendCSRollForward` carrying the header/tip
-- pair the relay is forwarding (`csSnxt csMust`, `NodeSpecs.agda:448`)
peer-pp2 : (i : Link) (d : Dir) (q : SN.CSsPos) (b : Block₃)
         → coarsenCSs q ≡ NS.csMust
         → absCSs i d q
             ─[ ev (evl (evLabel (Header × Tip) (apiCS i d sendCSRollForward)
                                 (header b , tip b))) ]─►
           absCSs i d (SN.ssRF1 (header b) (tip b))
peer-pp2 i d q b pin =
  aCSs i d q (SN.ssRF1 (header b) (tip b))
    (subst (λ z → NS.csSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csSnxt i d z ((Header × Tip) , apiCS i d sendCSRollForward)
                    (header b , tip b) ≡ just (NS.csWrf (header b , tip b)))
           (sym pin) (ceqCSs07 i d))

-- (pp3)  the down BF SERVER at `bsAreq r` offers `reqBFRange` carrying its own
-- recorded range (`bfSnxt bsAreq`, `NodeSpecs.agda:596-600`, gated `x ≟ r`)
peer-pp3 : (i : Link) (d : Dir) (q : SN.BFsPos) (r : ChainRange)
         → coarsenBFs q ≡ NS.bsAreq r
         → absBFs i d q ─[ ev (evl (evLabel ChainRange (apiBF i d reqBFRange) r)) ]─►
           absBFs i d (SN.bsHead BF.stBusy)
peer-pp3 i d q r pin =
  aBFs i d q (SN.bsHead BF.stBusy)
    (subst (λ z → NS.bfSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfSnxt i d z (ChainRange , apiBF i d reqBFRange) r
                  ≡ just NS.bsBusy)
           (sym pin) (ceqBFs07 i d))

-- (pp4)  … at `bsBusy` it offers `sendBFStartBatch` (`bfSnxt bsBusy`,
-- `NodeSpecs.agda:604-606`)
peer-pp4 : (i : Link) (d : Dir) (q : SN.BFsPos)
         → coarsenBFs q ≡ NS.bsBusy
         → absBFs i d q ─[ ev (evl (evLabel U.⊤ (apiBF i d sendBFStartBatch) U.tt)) ]─►
           absBFs i d SN.bsStart1
peer-pp4 i d q pin =
  aBFs i d q SN.bsStart1
    (subst (λ z → NS.bfSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfSnxt i d z (U.⊤ , apiBF i d sendBFStartBatch) U.tt
                  ≡ just NS.bsWsb)
           (sym pin) (ceqBFs03 i d))

-- (pp5)  … and at `bsStream` it offers `sendBFBlock` carrying the block
-- (`bfSnxt bsStream`, `NodeSpecs.agda:622-624`)
peer-pp5 : (i : Link) (d : Dir) (q : SN.BFsPos) (b : Block₃)
         → coarsenBFs q ≡ NS.bsStream
         → absBFs i d q ─[ ev (evl (evLabel Block₃ (apiBF i d sendBFBlock) b)) ]─►
           absBFs i d (SN.bsBlk1 b)
peer-pp5 i d q b pin =
  aBFs i d q (SN.bsBlk1 b)
    (subst (λ z → NS.bfSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfSnxt i d z (Block₃ , apiBF i d sendBFBlock) b
                  ≡ just (NS.bsWblk b))
           (sym pin) (ceqBFs05 i d))

------------------------------------------------------------------------
-- §3  THE NINE DRIVER OFFERS — the relay driver's own api offer at each
-- sub-phase, generic in BOTH links and in the carried block.
--
-- Each is two lines: a `viewV` equation on the phase's decode (the prefix's own
-- offer map, with `≟-yes-refl` unsticking the link comparison inside
-- `Net_Api-≟`, and the carried value's comparison too where the prefix is an
-- OUTPUT rather than an input), and the `sVis` that packages it.  The CONSUME
-- sub-phases additionally ride `TraceLawsBind.bind-ev`, since the relay's
-- consume tail sits under `>>= λ b′ → produce l₂ hi b′` — `bind-ev` is generic
-- in the continuation, so nothing here duplicates node D's `consD-offer-*`.
--
-- THE `cp6 ≡ pp0` COLLAPSE, machine-checked below by `relay-offer-cp6` being
-- literally `relay-offer-pp0`: `decCons l₁ hi b cp6` is `Ret b`, and
-- `force (P >>= k)` at a `ret r` IS `force (k r)` (`CSP/Operators.agda:338`) —
-- no intervening `sil`.
------------------------------------------------------------------------

-- (cp4)  the consume tail's `sendBFClientDone` prefix offers its ONE event; the
-- carried value is `U.tt`, so the OUTPUT's value gate closes by computation
consVis-cp4 : (i : Link) (b : Block₃)
  → viewV (PTree.force (decCons i hi b cp4)) (U.⊤ , apiBF i hi sendBFClientDone) U.tt
    ≡ just (decCons i hi b cp5)
consVis-cp4 i b rewrite ≟-yes-refl i = refl

-- … and the relay driver at `consuming b cp4` therefore offers it
relay-offer-cp4 : (l₁ l₂ : Link) (b : Block₃)
  → IoOffers (decCP l₁ l₂ (consuming b cp4)) (apiBF l₁ hi sendBFClientDone) U.tt
relay-offer-cp4 l₁ l₂ b =
    _
  , TLB.bind-ev (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp4)
      (sVis refl (consVis-cp4 l₁ b))

-- (cp5)  the consume tail's `sendCSDone` prefix (a `⟶₀`, i.e. an INPUT prefix
-- offering every value of the payload-free carrier)
consVis-cp5 : (i : Link) (b : Block₃)
  → viewV (PTree.force (decCons i hi b cp5)) (U.⊤ , apiCS i hi sendCSDone) U.tt
    ≡ just (decCons i hi b cp6)
consVis-cp5 i b rewrite ≟-yes-refl i = refl

-- … the relay driver at `consuming b cp5`
relay-offer-cp5 : (l₁ l₂ : Link) (b : Block₃)
  → IoOffers (decCP l₁ l₂ (consuming b cp5)) (apiCS l₁ hi sendCSDone) U.tt
relay-offer-cp5 l₁ l₂ b =
    _
  , TLB.bind-ev (λ b′ → produce l₂ hi b′) (decCons l₁ hi b cp5)
      (sVis refl (consVis-cp5 l₁ b))

-- (pp0)  the produce head's `reqCSRequestNext` prefix
prodVis-pp0 : (i : Link) (b : Block₃)
  → viewV (PTree.force (decProd i hi b pp0)) (U.⊤ , apiCS i hi reqCSRequestNext) U.tt
    ≡ just (decProd i hi b pp1)
prodVis-pp0 i b rewrite ≟-yes-refl i = refl

-- … the relay driver at `producing b pp0`
relay-offer-pp0 : (l₁ l₂ : Link) (b : Block₃)
  → IoOffers (decCP l₁ l₂ (producing b pp0)) (apiCS l₂ hi reqCSRequestNext) U.tt
relay-offer-pp0 l₁ l₂ b = _ , sVis refl (prodVis-pp0 l₂ b)

-- *** (cp6) THE COLLAPSE. ***  the relay driver at `consuming b cp6` offers
-- EXACTLY what it offers at `producing b pp0`, because the two trees are
-- definitionally equal — this definition is `relay-offer-pp0` verbatim, and that
-- it typechecks IS the machine-checked form of the claim
relay-offer-cp6 : (l₁ l₂ : Link) (b : Block₃)
  → IoOffers (decCP l₁ l₂ (consuming b cp6)) (apiCS l₂ hi reqCSRequestNext) U.tt
relay-offer-cp6 l₁ l₂ b = _ , sVis refl (prodVis-pp0 l₂ b)

-- (pp1)  the `sendCSAwaitReply` prefix
prodVis-pp1 : (i : Link) (b : Block₃)
  → viewV (PTree.force (decProd i hi b pp1)) (U.⊤ , apiCS i hi sendCSAwaitReply) U.tt
    ≡ just (decProd i hi b pp2)
prodVis-pp1 i b rewrite ≟-yes-refl i = refl

-- … the relay driver at `producing b pp1`
relay-offer-pp1 : (l₁ l₂ : Link) (b : Block₃)
  → IoOffers (decCP l₁ l₂ (producing b pp1)) (apiCS l₂ hi sendCSAwaitReply) U.tt
relay-offer-pp1 l₁ l₂ b = _ , sVis refl (prodVis-pp1 l₂ b)

-- (pp2)  the `sendCSRollForward` OUTPUT prefix: its value gate is the header/tip
-- pair built from the relayed block, so the value comparison needs unsticking too
prodVis-pp2 : (i : Link) (b : Block₃)
  → viewV (PTree.force (decProd i hi b pp2)) ((Header × Tip) , apiCS i hi sendCSRollForward)
      (header b , tip b)
    ≡ just (decProd i hi b pp3)
prodVis-pp2 i b rewrite ≟-yes-refl i | ≟-yes-refl (header b , tip b) = refl

-- … the relay driver at `producing b pp2`
relay-offer-pp2 : (l₁ l₂ : Link) (b : Block₃)
  → IoOffers (decCP l₁ l₂ (producing b pp2)) (apiCS l₂ hi sendCSRollForward)
      (header b , tip b)
relay-offer-pp2 l₁ l₂ b = _ , sVis refl (prodVis-pp2 l₂ b)

-- (pp3)  the `reqBFRange` INPUT prefix: it offers EVERY range, so the co-party's
-- own recorded range is the one that fires
prodVis-pp3 : (i : Link) (b : Block₃) (r : ChainRange)
  → viewV (PTree.force (decProd i hi b pp3)) (ChainRange , apiBF i hi reqBFRange) r
    ≡ just (decProd i hi b pp4)
prodVis-pp3 i b r rewrite ≟-yes-refl i = refl

-- … the relay driver at `producing b pp3`
relay-offer-pp3 : (l₁ l₂ : Link) (b : Block₃) (r : ChainRange)
  → IoOffers (decCP l₁ l₂ (producing b pp3)) (apiBF l₂ hi reqBFRange) r
relay-offer-pp3 l₁ l₂ b r = _ , sVis refl (prodVis-pp3 l₂ b r)

-- (pp4)  the `sendBFStartBatch` OUTPUT prefix at `U.tt`
prodVis-pp4 : (i : Link) (b : Block₃)
  → viewV (PTree.force (decProd i hi b pp4)) (U.⊤ , apiBF i hi sendBFStartBatch) U.tt
    ≡ just (decProd i hi b pp5)
prodVis-pp4 i b rewrite ≟-yes-refl i = refl

-- … the relay driver at `producing b pp4`
relay-offer-pp4 : (l₁ l₂ : Link) (b : Block₃)
  → IoOffers (decCP l₁ l₂ (producing b pp4)) (apiBF l₂ hi sendBFStartBatch) U.tt
relay-offer-pp4 l₁ l₂ b = _ , sVis refl (prodVis-pp4 l₂ b)

-- (pp5)  the `sendBFBlock` OUTPUT prefix: the value is the relayed BLOCK, so the
-- block comparison needs unsticking (this is the one sub-phase whose event is
-- KEPT on an UP link — see §4's hidden-ness note, where the DOWN link makes it
-- hidden by `keptB`'s link disjunct alone)
prodVis-pp5 : (i : Link) (b : Block₃)
  → viewV (PTree.force (decProd i hi b pp5)) (Block₃ , apiBF i hi sendBFBlock) b
    ≡ just (decProd i hi b pp6)
prodVis-pp5 i b rewrite ≟-yes-refl i | ≟-yes-refl b = refl

-- … the relay driver at `producing b pp5`
relay-offer-pp5 : (l₁ l₂ : Link) (b : Block₃)
  → IoOffers (decCP l₁ l₂ (producing b pp5)) (apiBF l₂ hi sendBFBlock) b
relay-offer-pp5 l₁ l₂ b = _ , sVis refl (prodVis-pp5 l₂ b)

------------------------------------------------------------------------
-- §4  THE FOUR SYNC KITS — "the co-party bundle steps AND the relay driver
-- offers the same event" ⇒ `⊥` from `isStable`.
--
-- The api hide arithmetic, re-derived at the point of use (it is
-- `LiveStableOffer` §10's, verbatim, and NOT the io one the cell/server families
-- ride): a node-internal `apiES` SYNC of a peer bundle with its driver lifts to
-- the four-node `⦀` (`nodes-offer-B`/`-C`, whose sibling-node refusals are keyed
-- on the event's LINK), goes SOLO past the medium because an api event is not in
-- `ioES` (`apiNodes-whole`), and is turned into a τ by the SECOND hide iff it is
-- in `hidden blkA` (`hiddenMove-⊥`).  No medium operand, hence no `broken`
-- hypothesis anywhere in this module.
--
-- There are FOUR kits and not one, because the relay node's two bundles are
-- keyed on DIFFERENT links and sit on different sides of the node's `⦀`: leg
-- BD's up bundle is node B's LEFT operand at `linkAB (hi, lo)` and its down
-- bundle the RIGHT one at `linkBD (lo, hi)`, and the same with node C for leg
-- CD.  Each kit is generic in the event, the carried value and the bundle's
-- successor, so all nine sub-phases of §5 ride these four.
------------------------------------------------------------------------

-- LEG BD, the UP bundle (node B's LEFT operand, `linkAB` at `(hi, lo)`)
syncUp-BD : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {B′ : NetProc}
  → IsApiCSBF ee → ApiHasLink linkAB ee → ApiIsCons ee
  → mem (hidden blkA) (X , ee) a → (ioES .mem (X , ee) a → ⊥)
  → apiES .mem (X , ee) a
  → absBundleG linkAB hi lo
      (SN.NodeStateB.csC-AB (nB (toSys r))) (SN.NodeStateB.csS-AB (nB (toSys r)))
      (SN.NodeStateB.bfC-AB (nB (toSys r))) (SN.NodeStateB.bfS-AB (nB (toSys r)))
      (SN.NodeStateB.inert-AB (nB (toSys r)))
      ─[ ev (evl (evLabel X ee a)) ]─► B′
  → IoOffers (decCP linkAB linkBD (SN.NodeStateB.cp-B (nB (toSys r)))) ee a
  → isStable (radec r ∖ hidden blkA) → ⊥
syncUp-BD r aic ahl aicons hid ¬io am bstep dOff sta =
  hiddenMove-⊥ r hid
    (apiNodes-whole r aic ¬io
      (nodes-offer-B (toSys r) am (inj₁ (aicons , ahl))
        ( _
        , lift-api-node-ev _ _ am
            (⦀-ev-L _ _ bstep
              (noOffer→viewV _
                (absBundleG-api-no linkBD lo hi
                   (SN.NodeStateB.csC-BD (nB (toSys r))) (SN.NodeStateB.csS-BD (nB (toSys r)))
                   (SN.NodeStateB.bfC-BD (nB (toSys r))) (SN.NodeStateB.bfS-BD (nB (toSys r)))
                   (SN.NodeStateB.inert-BD (nB (toSys r)))
                   ahl linkAB≢linkBD am)))
            (proj₂ dOff))))
    sta

-- LEG BD, the DOWN bundle (node B's RIGHT operand, `linkBD` at `(lo, hi)`)
syncDn-BD : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {B′ : NetProc}
  → IsApiCSBF ee → ApiHasLink linkBD ee → ApiIsProd ee
  → mem (hidden blkA) (X , ee) a → (ioES .mem (X , ee) a → ⊥)
  → apiES .mem (X , ee) a
  → absBundleG linkBD lo hi
      (SN.NodeStateB.csC-BD (nB (toSys r))) (SN.NodeStateB.csS-BD (nB (toSys r)))
      (SN.NodeStateB.bfC-BD (nB (toSys r))) (SN.NodeStateB.bfS-BD (nB (toSys r)))
      (SN.NodeStateB.inert-BD (nB (toSys r)))
      ─[ ev (evl (evLabel X ee a)) ]─► B′
  → IoOffers (decCP linkAB linkBD (SN.NodeStateB.cp-B (nB (toSys r)))) ee a
  → isStable (radec r ∖ hidden blkA) → ⊥
syncDn-BD r aic ahl aiprod hid ¬io am bstep dOff sta =
  hiddenMove-⊥ r hid
    (apiNodes-whole r aic ¬io
      (nodes-offer-B (toSys r) am (inj₂ (aiprod , ahl))
        ( _
        , lift-api-node-ev _ _ am
            (⦀-ev-R _ _ bstep
              (noOffer→viewV _
                (absBundleG-api-no linkAB hi lo
                   (SN.NodeStateB.csC-AB (nB (toSys r))) (SN.NodeStateB.csS-AB (nB (toSys r)))
                   (SN.NodeStateB.bfC-AB (nB (toSys r))) (SN.NodeStateB.bfS-AB (nB (toSys r)))
                   (SN.NodeStateB.inert-AB (nB (toSys r)))
                   ahl linkBD≢linkAB am)))
            (proj₂ dOff))))
    sta

-- LEG CD, the UP bundle (node C's LEFT operand, `linkAC` at `(hi, lo)`)
syncUp-CD : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {B′ : NetProc}
  → IsApiCSBF ee → ApiHasLink linkAC ee → ApiIsCons ee
  → mem (hidden blkA) (X , ee) a → (ioES .mem (X , ee) a → ⊥)
  → apiES .mem (X , ee) a
  → absBundleG linkAC hi lo
      (SN.NodeStateC.csC-AC (nC (toSys r))) (SN.NodeStateC.csS-AC (nC (toSys r)))
      (SN.NodeStateC.bfC-AC (nC (toSys r))) (SN.NodeStateC.bfS-AC (nC (toSys r)))
      (SN.NodeStateC.inert-AC (nC (toSys r)))
      ─[ ev (evl (evLabel X ee a)) ]─► B′
  → IoOffers (decCP linkAC linkCD (SN.NodeStateC.cp-C (nC (toSys r)))) ee a
  → isStable (radec r ∖ hidden blkA) → ⊥
syncUp-CD r aic ahl aicons hid ¬io am bstep dOff sta =
  hiddenMove-⊥ r hid
    (apiNodes-whole r aic ¬io
      (nodes-offer-C (toSys r) am (inj₁ (aicons , ahl))
        ( _
        , lift-api-node-ev _ _ am
            (⦀-ev-L _ _ bstep
              (noOffer→viewV _
                (absBundleG-api-no linkCD lo hi
                   (SN.NodeStateC.csC-CD (nC (toSys r))) (SN.NodeStateC.csS-CD (nC (toSys r)))
                   (SN.NodeStateC.bfC-CD (nC (toSys r))) (SN.NodeStateC.bfS-CD (nC (toSys r)))
                   (SN.NodeStateC.inert-CD (nC (toSys r)))
                   ahl linkAC≢linkCD am)))
            (proj₂ dOff))))
    sta

-- LEG CD, the DOWN bundle (node C's RIGHT operand, `linkCD` at `(lo, hi)`)
syncDn-CD : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {B′ : NetProc}
  → IsApiCSBF ee → ApiHasLink linkCD ee → ApiIsProd ee
  → mem (hidden blkA) (X , ee) a → (ioES .mem (X , ee) a → ⊥)
  → apiES .mem (X , ee) a
  → absBundleG linkCD lo hi
      (SN.NodeStateC.csC-CD (nC (toSys r))) (SN.NodeStateC.csS-CD (nC (toSys r)))
      (SN.NodeStateC.bfC-CD (nC (toSys r))) (SN.NodeStateC.bfS-CD (nC (toSys r)))
      (SN.NodeStateC.inert-CD (nC (toSys r)))
      ─[ ev (evl (evLabel X ee a)) ]─► B′
  → IoOffers (decCP linkAC linkCD (SN.NodeStateC.cp-C (nC (toSys r)))) ee a
  → isStable (radec r ∖ hidden blkA) → ⊥
syncDn-CD r aic ahl aiprod hid ¬io am bstep dOff sta =
  hiddenMove-⊥ r hid
    (apiNodes-whole r aic ¬io
      (nodes-offer-C (toSys r) am (inj₂ (aiprod , ahl))
        ( _
        , lift-api-node-ev _ _ am
            (⦀-ev-R _ _ bstep
              (noOffer→viewV _
                (absBundleG-api-no linkAC hi lo
                   (SN.NodeStateC.csC-AC (nC (toSys r))) (SN.NodeStateC.csS-AC (nC (toSys r)))
                   (SN.NodeStateC.bfC-AC (nC (toSys r))) (SN.NodeStateC.bfS-AC (nC (toSys r)))
                   (SN.NodeStateC.inert-AC (nC (toSys r)))
                   ahl linkCD≢linkAC am)))
            (proj₂ dOff))))
    sta


------------------------------------------------------------------------
-- §5  THE NINE ARM THEOREMS.
--
-- Each is "the relay driver is at THIS sub-phase and its co-party is at the
-- position that accepts the driver's event ⇒ the configuration is not stable".
-- Every one is a THEOREM with exactly TWO hypotheses beyond the leg and the
-- config: the driver's own phase equation (which §6's dispatch supplies out of
-- `AtPos`) and ONE coarse-position equation on the co-party slot named in the
-- module header's table.  No `broken`, no `ChanUp`/`ChanDn`, no `NoTwoTokens`.
--
-- THE LEG DISPATCH IS ON AN EXPLICIT `TwoLegs` ARGUMENT (never a `with`) and it
-- has to be, for the reason `LiveSrvOpen` §2 records: the accessors reduce to a
-- literal link and a literal peer slot only after the leg is a constructor, and
-- the four sync kits are those literals' own.  The leg-generic delegate shape the
-- Task-2c review asks for is used where it CAN be — §2's peer offers and §3's
-- driver offers are generic in the link, the direction and the carried value, so
-- each pair of clauses below is two APPLICATIONS of one lemma pair, not two
-- proofs.  MEASURED DEVIATION, disclosed: the bundle lift `absBundle-*-ev` cannot
-- take `_` for the eleven passenger positions — `absBundleG` is stated on FINE
-- positions and reduces through `coarsen*`, so unification blocks on
-- `coarsen* _q = coarsen* (field …)` (the `[UnsolvedConstraints]` this module hit
-- on its first build).  Every passenger and every successor position is therefore
-- named explicitly; that, not the leg split, is the bulk of §5's line count.
--
-- The hidden-ness side conditions are all `refl`: `keptB`'s only two non-`break`
-- clauses are `sendBFBlock` and `recvBFBlock` (`Spec.lagda.md:109-115`), so seven
-- of the nine events fall to its catch-all with no link, dir or block test
-- consulted; and the two `sendBFBlock` arms (pp5) are on a DOWN link, where
-- `keptB`'s send clause tests `(l ≟ linkAB) ∨ (l ≟ linkAC)` and short-circuits to
-- `false` before the block is ever compared.
------------------------------------------------------------------------

-- (cp4)  the consume tail's client-done handshake fires with the up BF client
arm-cp4 : (l : TwoLegs) (r : RState) (b : Block₃)
        → relayOf l (toSys r) ≡ consuming b cp4
        → coarsenBFc (upClient l (toSys r)) ≡ NS.bcIdle
        → isStable (radec r ∖ hidden blkA) → ⊥
arm-cp4 legBD r b hcp pin sta =
  syncUp-BD r aicBF ahlBF aicBFdone refl (λ ()) tt
    (absBundle-BFc-ev linkAB hi lo (SN.NodeStateB.csC-AB (nB (toSys r))) (SN.NodeStateB.csS-AB (nB (toSys r))) (SN.NodeStateB.bfC-AB (nB (toSys r))) (SN.NodeStateB.bfS-AB (nB (toSys r))) (SN.NodeStateB.inert-AB (nB (toSys r)))
       {e₁ = BF.apiBFev linkAB hi sendBFClientDone} {qbc′ = SN.bcDone1} (λ ()) refl
       (peer-cp4 linkAB hi (SN.NodeStateB.bfC-AB (nB (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAB linkBD q) (apiBF linkAB hi sendBFClientDone) U.tt)
           (sym hcp) (relay-offer-cp4 linkAB linkBD b))
    sta
arm-cp4 legCD r b hcp pin sta =
  syncUp-CD r aicBF ahlBF aicBFdone refl (λ ()) tt
    (absBundle-BFc-ev linkAC hi lo (SN.NodeStateC.csC-AC (nC (toSys r))) (SN.NodeStateC.csS-AC (nC (toSys r))) (SN.NodeStateC.bfC-AC (nC (toSys r))) (SN.NodeStateC.bfS-AC (nC (toSys r))) (SN.NodeStateC.inert-AC (nC (toSys r)))
       {e₁ = BF.apiBFev linkAC hi sendBFClientDone} {qbc′ = SN.bcDone1} (λ ()) refl
       (peer-cp4 linkAC hi (SN.NodeStateC.bfC-AC (nC (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAC linkCD q) (apiBF linkAC hi sendBFClientDone) U.tt)
           (sym hcp) (relay-offer-cp4 linkAC linkCD b))
    sta

-- (cp5)  … and the ChainSync done handshake with the up CS client
arm-cp5 : (l : TwoLegs) (r : RState) (b : Block₃)
        → relayOf l (toSys r) ≡ consuming b cp5
        → coarsenCSc (upCSc l (toSys r)) ≡ NS.ccIdle
        → isStable (radec r ∖ hidden blkA) → ⊥
arm-cp5 legBD r b hcp pin sta =
  syncUp-BD r aicCS ahlCS aicCSdone refl (λ ()) tt
    (absBundle-CSc-ev linkAB hi lo (SN.NodeStateB.csC-AB (nB (toSys r))) (SN.NodeStateB.csS-AB (nB (toSys r))) (SN.NodeStateB.bfC-AB (nB (toSys r))) (SN.NodeStateB.bfS-AB (nB (toSys r))) (SN.NodeStateB.inert-AB (nB (toSys r)))
       {e₁ = CS.apiCSev linkAB hi sendCSDone} {qcc′ = SN.csDone1} (λ ()) refl
       (peer-cp5 linkAB hi (SN.NodeStateB.csC-AB (nB (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAB linkBD q) (apiCS linkAB hi sendCSDone) U.tt)
           (sym hcp) (relay-offer-cp5 linkAB linkBD b))
    sta
arm-cp5 legCD r b hcp pin sta =
  syncUp-CD r aicCS ahlCS aicCSdone refl (λ ()) tt
    (absBundle-CSc-ev linkAC hi lo (SN.NodeStateC.csC-AC (nC (toSys r))) (SN.NodeStateC.csS-AC (nC (toSys r))) (SN.NodeStateC.bfC-AC (nC (toSys r))) (SN.NodeStateC.bfS-AC (nC (toSys r))) (SN.NodeStateC.inert-AC (nC (toSys r)))
       {e₁ = CS.apiCSev linkAC hi sendCSDone} {qcc′ = SN.csDone1} (λ ()) refl
       (peer-cp5 linkAC hi (SN.NodeStateC.csC-AC (nC (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAC linkCD q) (apiCS linkAC hi sendCSDone) U.tt)
           (sym hcp) (relay-offer-cp5 linkAC linkCD b))
    sta

-- (cp6)  the bind hop: the `Ret` collapses into the produce head, so the relay
-- ALREADY offers `reqCSRequestNext` to its DOWN CS server at `cp6`
arm-cp6 : (l : TwoLegs) (r : RState) (b : Block₃)
        → relayOf l (toSys r) ≡ consuming b cp6
        → coarsenCSs (dnCSs l (toSys r)) ≡ NS.csAreq
        → isStable (radec r ∖ hidden blkA) → ⊥
arm-cp6 legBD r b hcp pin sta =
  syncDn-BD r aicCS ahlCS aipCSreq refl (λ ()) tt
    (absBundle-CSs-ev linkBD lo hi (SN.NodeStateB.csC-BD (nB (toSys r))) (SN.NodeStateB.csS-BD (nB (toSys r))) (SN.NodeStateB.bfC-BD (nB (toSys r))) (SN.NodeStateB.bfS-BD (nB (toSys r))) (SN.NodeStateB.inert-BD (nB (toSys r)))
       {e₁ = CS.apiCSev linkBD hi reqCSRequestNext} {qcs′ = SN.ssHead CS.stCanAwait} (λ ()) refl
       (peer-pp0 linkBD hi (SN.NodeStateB.csS-BD (nB (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAB linkBD q) (apiCS linkBD hi reqCSRequestNext) U.tt)
           (sym hcp) (relay-offer-cp6 linkAB linkBD b))
    sta
arm-cp6 legCD r b hcp pin sta =
  syncDn-CD r aicCS ahlCS aipCSreq refl (λ ()) tt
    (absBundle-CSs-ev linkCD lo hi (SN.NodeStateC.csC-CD (nC (toSys r))) (SN.NodeStateC.csS-CD (nC (toSys r))) (SN.NodeStateC.bfC-CD (nC (toSys r))) (SN.NodeStateC.bfS-CD (nC (toSys r))) (SN.NodeStateC.inert-CD (nC (toSys r)))
       {e₁ = CS.apiCSev linkCD hi reqCSRequestNext} {qcs′ = SN.ssHead CS.stCanAwait} (λ ()) refl
       (peer-pp0 linkCD hi (SN.NodeStateC.csS-CD (nC (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAC linkCD q) (apiCS linkCD hi reqCSRequestNext) U.tt)
           (sym hcp) (relay-offer-cp6 linkAC linkCD b))
    sta

-- (pp0)  the same event, from the produce head proper
arm-pp0 : (l : TwoLegs) (r : RState) (b : Block₃)
        → relayOf l (toSys r) ≡ producing b pp0
        → coarsenCSs (dnCSs l (toSys r)) ≡ NS.csAreq
        → isStable (radec r ∖ hidden blkA) → ⊥
arm-pp0 legBD r b hcp pin sta =
  syncDn-BD r aicCS ahlCS aipCSreq refl (λ ()) tt
    (absBundle-CSs-ev linkBD lo hi (SN.NodeStateB.csC-BD (nB (toSys r))) (SN.NodeStateB.csS-BD (nB (toSys r))) (SN.NodeStateB.bfC-BD (nB (toSys r))) (SN.NodeStateB.bfS-BD (nB (toSys r))) (SN.NodeStateB.inert-BD (nB (toSys r)))
       {e₁ = CS.apiCSev linkBD hi reqCSRequestNext} {qcs′ = SN.ssHead CS.stCanAwait} (λ ()) refl
       (peer-pp0 linkBD hi (SN.NodeStateB.csS-BD (nB (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAB linkBD q) (apiCS linkBD hi reqCSRequestNext) U.tt)
           (sym hcp) (relay-offer-pp0 linkAB linkBD b))
    sta
arm-pp0 legCD r b hcp pin sta =
  syncDn-CD r aicCS ahlCS aipCSreq refl (λ ()) tt
    (absBundle-CSs-ev linkCD lo hi (SN.NodeStateC.csC-CD (nC (toSys r))) (SN.NodeStateC.csS-CD (nC (toSys r))) (SN.NodeStateC.bfC-CD (nC (toSys r))) (SN.NodeStateC.bfS-CD (nC (toSys r))) (SN.NodeStateC.inert-CD (nC (toSys r)))
       {e₁ = CS.apiCSev linkCD hi reqCSRequestNext} {qcs′ = SN.ssHead CS.stCanAwait} (λ ()) refl
       (peer-pp0 linkCD hi (SN.NodeStateC.csS-CD (nC (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAC linkCD q) (apiCS linkCD hi reqCSRequestNext) U.tt)
           (sym hcp) (relay-offer-pp0 linkAC linkCD b))
    sta

-- (pp1)  the Praos-faithful `AwaitReply` detour
arm-pp1 : (l : TwoLegs) (r : RState) (b : Block₃)
        → relayOf l (toSys r) ≡ producing b pp1
        → coarsenCSs (dnCSs l (toSys r)) ≡ NS.csCanAwait
        → isStable (radec r ∖ hidden blkA) → ⊥
arm-pp1 legBD r b hcp pin sta =
  syncDn-BD r aicCS ahlCS aipCSawait refl (λ ()) tt
    (absBundle-CSs-ev linkBD lo hi (SN.NodeStateB.csC-BD (nB (toSys r))) (SN.NodeStateB.csS-BD (nB (toSys r))) (SN.NodeStateB.bfC-BD (nB (toSys r))) (SN.NodeStateB.bfS-BD (nB (toSys r))) (SN.NodeStateB.inert-BD (nB (toSys r)))
       {e₁ = CS.apiCSev linkBD hi sendCSAwaitReply} {qcs′ = SN.ssAw1} (λ ()) refl
       (peer-pp1 linkBD hi (SN.NodeStateB.csS-BD (nB (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAB linkBD q) (apiCS linkBD hi sendCSAwaitReply) U.tt)
           (sym hcp) (relay-offer-pp1 linkAB linkBD b))
    sta
arm-pp1 legCD r b hcp pin sta =
  syncDn-CD r aicCS ahlCS aipCSawait refl (λ ()) tt
    (absBundle-CSs-ev linkCD lo hi (SN.NodeStateC.csC-CD (nC (toSys r))) (SN.NodeStateC.csS-CD (nC (toSys r))) (SN.NodeStateC.bfC-CD (nC (toSys r))) (SN.NodeStateC.bfS-CD (nC (toSys r))) (SN.NodeStateC.inert-CD (nC (toSys r)))
       {e₁ = CS.apiCSev linkCD hi sendCSAwaitReply} {qcs′ = SN.ssAw1} (λ ()) refl
       (peer-pp1 linkCD hi (SN.NodeStateC.csS-CD (nC (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAC linkCD q) (apiCS linkCD hi sendCSAwaitReply) U.tt)
           (sym hcp) (relay-offer-pp1 linkAC linkCD b))
    sta

-- (pp2)  the header push, carrying the relayed block's own header/tip pair
arm-pp2 : (l : TwoLegs) (r : RState) (b : Block₃)
        → relayOf l (toSys r) ≡ producing b pp2
        → coarsenCSs (dnCSs l (toSys r)) ≡ NS.csMust
        → isStable (radec r ∖ hidden blkA) → ⊥
arm-pp2 legBD r b hcp pin sta =
  syncDn-BD r aicCS ahlCS aipCSroll refl (λ ()) tt
    (absBundle-CSs-ev linkBD lo hi (SN.NodeStateB.csC-BD (nB (toSys r))) (SN.NodeStateB.csS-BD (nB (toSys r))) (SN.NodeStateB.bfC-BD (nB (toSys r))) (SN.NodeStateB.bfS-BD (nB (toSys r))) (SN.NodeStateB.inert-BD (nB (toSys r)))
       {e₁ = CS.apiCSev linkBD hi sendCSRollForward} {qcs′ = SN.ssRF1 (header b) (tip b)} (λ ()) refl
       (peer-pp2 linkBD hi (SN.NodeStateB.csS-BD (nB (toSys r))) b pin))
    (subst (λ q → IoOffers (decCP linkAB linkBD q) (apiCS linkBD hi sendCSRollForward) (header b , tip b))
           (sym hcp) (relay-offer-pp2 linkAB linkBD b))
    sta
arm-pp2 legCD r b hcp pin sta =
  syncDn-CD r aicCS ahlCS aipCSroll refl (λ ()) tt
    (absBundle-CSs-ev linkCD lo hi (SN.NodeStateC.csC-CD (nC (toSys r))) (SN.NodeStateC.csS-CD (nC (toSys r))) (SN.NodeStateC.bfC-CD (nC (toSys r))) (SN.NodeStateC.bfS-CD (nC (toSys r))) (SN.NodeStateC.inert-CD (nC (toSys r)))
       {e₁ = CS.apiCSev linkCD hi sendCSRollForward} {qcs′ = SN.ssRF1 (header b) (tip b)} (λ ()) refl
       (peer-pp2 linkCD hi (SN.NodeStateC.csS-CD (nC (toSys r))) b pin))
    (subst (λ q → IoOffers (decCP linkAC linkCD q) (apiCS linkCD hi sendCSRollForward) (header b , tip b))
           (sym hcp) (relay-offer-pp2 linkAC linkCD b))
    sta

-- (pp3)  the range request: the driver's prefix offers EVERY range, so the
-- co-party's own recorded range is what fires
arm-pp3 : (l : TwoLegs) (r : RState) (b : Block₃) (rg : ChainRange)
        → relayOf l (toSys r) ≡ producing b pp3
        → coarsenBFs (dnSrv l (toSys r)) ≡ NS.bsAreq rg
        → isStable (radec r ∖ hidden blkA) → ⊥
arm-pp3 legBD r b rg hcp pin sta =
  syncDn-BD r aicBF ahlBF aipBFreq refl (λ ()) tt
    (absBundle-BFs-ev linkBD lo hi (SN.NodeStateB.csC-BD (nB (toSys r))) (SN.NodeStateB.csS-BD (nB (toSys r))) (SN.NodeStateB.bfC-BD (nB (toSys r))) (SN.NodeStateB.bfS-BD (nB (toSys r))) (SN.NodeStateB.inert-BD (nB (toSys r)))
       {e₁ = BF.apiBFev linkBD hi reqBFRange} {qbs′ = SN.bsHead BF.stBusy} (λ ()) refl
       (peer-pp3 linkBD hi (SN.NodeStateB.bfS-BD (nB (toSys r))) rg pin))
    (subst (λ q → IoOffers (decCP linkAB linkBD q) (apiBF linkBD hi reqBFRange) rg)
           (sym hcp) (relay-offer-pp3 linkAB linkBD b rg))
    sta
arm-pp3 legCD r b rg hcp pin sta =
  syncDn-CD r aicBF ahlBF aipBFreq refl (λ ()) tt
    (absBundle-BFs-ev linkCD lo hi (SN.NodeStateC.csC-CD (nC (toSys r))) (SN.NodeStateC.csS-CD (nC (toSys r))) (SN.NodeStateC.bfC-CD (nC (toSys r))) (SN.NodeStateC.bfS-CD (nC (toSys r))) (SN.NodeStateC.inert-CD (nC (toSys r)))
       {e₁ = BF.apiBFev linkCD hi reqBFRange} {qbs′ = SN.bsHead BF.stBusy} (λ ()) refl
       (peer-pp3 linkCD hi (SN.NodeStateC.bfS-CD (nC (toSys r))) rg pin))
    (subst (λ q → IoOffers (decCP linkAC linkCD q) (apiBF linkCD hi reqBFRange) rg)
           (sym hcp) (relay-offer-pp3 linkAC linkCD b rg))
    sta

-- (pp4)  the batch opening
arm-pp4 : (l : TwoLegs) (r : RState) (b : Block₃)
        → relayOf l (toSys r) ≡ producing b pp4
        → coarsenBFs (dnSrv l (toSys r)) ≡ NS.bsBusy
        → isStable (radec r ∖ hidden blkA) → ⊥
arm-pp4 legBD r b hcp pin sta =
  syncDn-BD r aicBF ahlBF aipBFstart refl (λ ()) tt
    (absBundle-BFs-ev linkBD lo hi (SN.NodeStateB.csC-BD (nB (toSys r))) (SN.NodeStateB.csS-BD (nB (toSys r))) (SN.NodeStateB.bfC-BD (nB (toSys r))) (SN.NodeStateB.bfS-BD (nB (toSys r))) (SN.NodeStateB.inert-BD (nB (toSys r)))
       {e₁ = BF.apiBFev linkBD hi sendBFStartBatch} {qbs′ = SN.bsStart1} (λ ()) refl
       (peer-pp4 linkBD hi (SN.NodeStateB.bfS-BD (nB (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAB linkBD q) (apiBF linkBD hi sendBFStartBatch) U.tt)
           (sym hcp) (relay-offer-pp4 linkAB linkBD b))
    sta
arm-pp4 legCD r b hcp pin sta =
  syncDn-CD r aicBF ahlBF aipBFstart refl (λ ()) tt
    (absBundle-BFs-ev linkCD lo hi (SN.NodeStateC.csC-CD (nC (toSys r))) (SN.NodeStateC.csS-CD (nC (toSys r))) (SN.NodeStateC.bfC-CD (nC (toSys r))) (SN.NodeStateC.bfS-CD (nC (toSys r))) (SN.NodeStateC.inert-CD (nC (toSys r)))
       {e₁ = BF.apiBFev linkCD hi sendBFStartBatch} {qbs′ = SN.bsStart1} (λ ()) refl
       (peer-pp4 linkCD hi (SN.NodeStateC.bfS-CD (nC (toSys r))) pin))
    (subst (λ q → IoOffers (decCP linkAC linkCD q) (apiBF linkCD hi sendBFStartBatch) U.tt)
           (sym hcp) (relay-offer-pp4 linkAC linkCD b))
    sta

-- (pp5)  the onward block send — the one arm whose event `keptB` inspects, and it
-- is HIDDEN here because the link is a DOWN one (the KEPT instance of this event
-- is A's, on `linkAB`/`linkAC`)
arm-pp5 : (l : TwoLegs) (r : RState) (b : Block₃)
        → relayOf l (toSys r) ≡ producing b pp5
        → coarsenBFs (dnSrv l (toSys r)) ≡ NS.bsStream
        → isStable (radec r ∖ hidden blkA) → ⊥
arm-pp5 legBD r b hcp pin sta =
  syncDn-BD r aicBF ahlBF aipBFblock refl (λ ()) tt
    (absBundle-BFs-ev linkBD lo hi (SN.NodeStateB.csC-BD (nB (toSys r))) (SN.NodeStateB.csS-BD (nB (toSys r))) (SN.NodeStateB.bfC-BD (nB (toSys r))) (SN.NodeStateB.bfS-BD (nB (toSys r))) (SN.NodeStateB.inert-BD (nB (toSys r)))
       {e₁ = BF.apiBFev linkBD hi sendBFBlock} {qbs′ = SN.bsBlk1 b} (λ ()) refl
       (peer-pp5 linkBD hi (SN.NodeStateB.bfS-BD (nB (toSys r))) b pin))
    (subst (λ q → IoOffers (decCP linkAB linkBD q) (apiBF linkBD hi sendBFBlock) b)
           (sym hcp) (relay-offer-pp5 linkAB linkBD b))
    sta
arm-pp5 legCD r b hcp pin sta =
  syncDn-CD r aicBF ahlBF aipBFblock refl (λ ()) tt
    (absBundle-BFs-ev linkCD lo hi (SN.NodeStateC.csC-CD (nC (toSys r))) (SN.NodeStateC.csS-CD (nC (toSys r))) (SN.NodeStateC.bfC-CD (nC (toSys r))) (SN.NodeStateC.bfS-CD (nC (toSys r))) (SN.NodeStateC.inert-CD (nC (toSys r)))
       {e₁ = BF.apiBFev linkCD hi sendBFBlock} {qbs′ = SN.bsBlk1 b} (λ ()) refl
       (peer-pp5 linkCD hi (SN.NodeStateC.bfS-CD (nC (toSys r))) b pin))
    (subst (λ q → IoOffers (decCP linkAC linkCD q) (apiBF linkCD hi sendBFBlock) b)
           (sym hcp) (relay-offer-pp5 linkAC linkCD b))
    sta
------------------------------------------------------------------------
-- §6  THE TWO TOTAL DISPATCHES, THE CO-POSITION PREDICATE, AND THE FOUR FACTS.
--
-- `AtPos l lpRelayIn b s` is `RelayIn⁺ b (relayOf l s) × ProdSent … × InCp03 …`
-- with `RelayIn⁺ b x = RelayIn x × (relayBlk x ≡ b)` (`LiveLegInv.agda:368-369`,
-- `:434-437`), so the position hands over exactly `RelayIn (relayOf l s)` — and
-- §6a RESOLVES that into the three sub-phase equations at the driver's own
-- recorded block, which is the `LiveStableOffer.relayCp3⇒form` move one hop
-- further along.  `ProdSent` and `InCp03` are NOT consumed by anything below;
-- they travel with the position and the api route has no use for them.
--
-- `CoAt` is ONE predicate for BOTH families, and that is not a shortcut: the two
-- positions occupy DISJOINT sub-phase regions of the same `CPPh` (`cp4..cp6` vs
-- `pp0..pp5`), so a single total dispatch on `CPPh` covers both with no clause
-- doing double duty.  It is a TOTAL dispatch — all seventeen `CPPh` shapes are
-- written out, no catch-all — so a new `ConsPh`/`ProdPh` constructor would be a
-- type error here rather than a silently-`⊤` arm.
------------------------------------------------------------------------

-- §6a  the consume-tail hold, RESOLVED into its three sub-phases at the driver's
-- own recorded block (the `relayCp3⇒form` mirror; `relayBlk (consuming b _) = b`)
relayIn⇒form : (x : CPPh) → RelayIn x
             → (x ≡ consuming (relayBlk x) cp4)
             ⊎ (x ≡ consuming (relayBlk x) cp5)
             ⊎ (x ≡ consuming (relayBlk x) cp6)
relayIn⇒form (consuming b cp0) ()
relayIn⇒form (consuming b cp1) ()
relayIn⇒form (consuming b cp2) ()
relayIn⇒form (consuming b cp3) ()
relayIn⇒form (consuming b cp4) _ = inj₁ refl
relayIn⇒form (consuming b cp5) _ = inj₂ (inj₁ refl)
relayIn⇒form (consuming b cp6) _ = inj₂ (inj₂ refl)
relayIn⇒form (producing b pp)  ()

-- … and the produce-tail hold, resolved into its SIX sub-phases
relayOut⇒form : (x : CPPh) → RelayOut x
              → (x ≡ producing (relayBlk x) pp0)
              ⊎ (x ≡ producing (relayBlk x) pp1)
              ⊎ (x ≡ producing (relayBlk x) pp2)
              ⊎ (x ≡ producing (relayBlk x) pp3)
              ⊎ (x ≡ producing (relayBlk x) pp4)
              ⊎ (x ≡ producing (relayBlk x) pp5)
relayOut⇒form (consuming b cp)  ()
relayOut⇒form (producing b pp0) _ = inj₁ refl
relayOut⇒form (producing b pp1) _ = inj₂ (inj₁ refl)
relayOut⇒form (producing b pp2) _ = inj₂ (inj₂ (inj₁ refl))
relayOut⇒form (producing b pp3) _ = inj₂ (inj₂ (inj₂ (inj₁ refl)))
relayOut⇒form (producing b pp4) _ = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl))))
relayOut⇒form (producing b pp5) _ = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ refl))))
relayOut⇒form (producing b pp6) ()
relayOut⇒form (producing b pp7) ()
relayOut⇒form (producing b pp8) ()
relayOut⇒form (producing b pp9) ()

-- §6b  *** THE CO-POSITION REQUIREMENT, PER SUB-PHASE. ***  A TOTAL dispatch on
-- `CPPh`: at each of the nine in-flight sub-phases it is the ONE coarse-position
-- equation §5's arm consumes, and at the other eight shapes it is `⊤` (the token
-- is not in the relay driver there, so `AtPos` never reaches them — the `⊤`s are
-- reachable only through `RelayIn`/`RelayOut`'s own absurd clauses above).
--
-- *** THIS IS THE MODULE'S RESIDUAL.  IT IS NOT DISCHARGED HERE, AND §7 SAYS
-- WHY AND WHAT IT COSTS.  Nothing in the campaign depends on it — the
-- `LiveTokenExcl.UpChainCp3`/`DnChainCp3` discipline. ***
--
-- *** AND DO NOT THREAD IT BARE. ***  As a bare state predicate it is FALSE at
-- reachable states (§7(a)); §6e gives the `isStable`-scoped forms, and those are
-- the ones a consumer may use.  `RelayCo` itself exists only as the body of that
-- implication.
CoAt : TwoLegs → SysState → CPPh → Set
CoAt l s (consuming _ cp0) = ⊤
CoAt l s (consuming _ cp1) = ⊤
CoAt l s (consuming _ cp2) = ⊤
CoAt l s (consuming _ cp3) = ⊤
CoAt l s (consuming _ cp4) = coarsenBFc (upClient l s) ≡ NS.bcIdle
CoAt l s (consuming _ cp5) = coarsenCSc (upCSc   l s) ≡ NS.ccIdle
CoAt l s (consuming _ cp6) = coarsenCSs (dnCSs   l s) ≡ NS.csAreq
CoAt l s (producing _ pp0) = coarsenCSs (dnCSs   l s) ≡ NS.csAreq
CoAt l s (producing _ pp1) = coarsenCSs (dnCSs   l s) ≡ NS.csCanAwait
CoAt l s (producing _ pp2) = coarsenCSs (dnCSs   l s) ≡ NS.csMust
CoAt l s (producing _ pp3) = Σ[ rg ∈ ChainRange ] (coarsenBFs (dnSrv l s) ≡ NS.bsAreq rg)
CoAt l s (producing _ pp4) = coarsenBFs (dnSrv   l s) ≡ NS.bsBusy
CoAt l s (producing _ pp5) = coarsenBFs (dnSrv   l s) ≡ NS.bsStream
CoAt l s (producing _ pp6) = ⊤
CoAt l s (producing _ pp7) = ⊤
CoAt l s (producing _ pp8) = ⊤
CoAt l s (producing _ pp9) = ⊤

-- the co-position requirement AT THE RELAY DRIVER'S ACTUAL PHASE — one premise
-- serving both facts, since `RelayIn` and `RelayOut` pin disjoint regions
RelayCo : TwoLegs → SysState → Set
RelayCo l s = CoAt l s (relayOf l s)

-- §6c  *** ARM `lpRelayIn`, BOTH LEGS. ***  A stable configuration cannot have
-- the token in the relay driver's CONSUME tail: the tail's three sub-phases each
-- offer one api event, and the co-position premise puts the co-party where it
-- accepts that event, so the sync is a hidden τ.
relayOpen-in : (l : TwoLegs) (r : RState)
             → RelayCo l (toSys r) → RefutedAt l lpRelayIn blkA r
relayOpen-in l r co at sta =
  arms (relayIn⇒form (relayOf l (toSys r)) (proj₁ (proj₁ at)))
  where
  arms : (relayOf l (toSys r) ≡ consuming (relayBlk (relayOf l (toSys r))) cp4)
       ⊎ (relayOf l (toSys r) ≡ consuming (relayBlk (relayOf l (toSys r))) cp5)
       ⊎ (relayOf l (toSys r) ≡ consuming (relayBlk (relayOf l (toSys r))) cp6)
       → ⊥
  arms (inj₁ eq) =
    arm-cp4 l r (relayBlk (relayOf l (toSys r))) eq (subst (CoAt l (toSys r)) eq co) sta
  arms (inj₂ (inj₁ eq)) =
    arm-cp5 l r (relayBlk (relayOf l (toSys r))) eq (subst (CoAt l (toSys r)) eq co) sta
  arms (inj₂ (inj₂ eq)) =
    arm-cp6 l r (relayBlk (relayOf l (toSys r))) eq (subst (CoAt l (toSys r)) eq co) sta

-- *** ARM `lpRelayOut`, BOTH LEGS. ***  … and not in its PRODUCE tail either:
-- there the six sub-phases drive the relay's own DOWN-link CS and BF servers.
relayOpen-out : (l : TwoLegs) (r : RState)
              → RelayCo l (toSys r) → RefutedAt l lpRelayOut blkA r
relayOpen-out l r co at sta =
  arms (relayOut⇒form (relayOf l (toSys r)) (proj₁ (proj₁ at)))
  where
  arms : (relayOf l (toSys r) ≡ producing (relayBlk (relayOf l (toSys r))) pp0)
       ⊎ (relayOf l (toSys r) ≡ producing (relayBlk (relayOf l (toSys r))) pp1)
       ⊎ (relayOf l (toSys r) ≡ producing (relayBlk (relayOf l (toSys r))) pp2)
       ⊎ (relayOf l (toSys r) ≡ producing (relayBlk (relayOf l (toSys r))) pp3)
       ⊎ (relayOf l (toSys r) ≡ producing (relayBlk (relayOf l (toSys r))) pp4)
       ⊎ (relayOf l (toSys r) ≡ producing (relayBlk (relayOf l (toSys r))) pp5)
       → ⊥
  arms (inj₁ eq) =
    arm-pp0 l r (relayBlk (relayOf l (toSys r))) eq (subst (CoAt l (toSys r)) eq co) sta
  arms (inj₂ (inj₁ eq)) =
    arm-pp1 l r (relayBlk (relayOf l (toSys r))) eq (subst (CoAt l (toSys r)) eq co) sta
  arms (inj₂ (inj₂ (inj₁ eq))) =
    arm-pp2 l r (relayBlk (relayOf l (toSys r))) eq (subst (CoAt l (toSys r)) eq co) sta
  arms (inj₂ (inj₂ (inj₂ (inj₁ eq)))) =
    arm-pp3 l r (relayBlk (relayOf l (toSys r))) (proj₁ (subst (CoAt l (toSys r)) eq co))
      eq (proj₂ (subst (CoAt l (toSys r)) eq co)) sta
  arms (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ eq))))) =
    arm-pp4 l r (relayBlk (relayOf l (toSys r))) eq (subst (CoAt l (toSys r)) eq co) sta
  arms (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ eq))))) =
    arm-pp5 l r (relayBlk (relayOf l (toSys r))) eq (subst (CoAt l (toSys r)) eq co) sta

------------------------------------------------------------------------
-- §6d  THE WINDOW COROLLARIES — the assembly's uniform shape.
--
-- The four cell facts and the four server facts each take their `broken … ≡
-- false` hypothesis off `LiveStableOffer.Window`'s two link fields
-- (`LiveCellOpen` §4, `LiveSrvOpen` §3), so the assembly wants all twelve fields
-- in one shape.  These two corollaries supply that shape.
--
-- WHAT IS AND IS NOT TRUE ABOUT THE WINDOW HERE.  What is true is that the api
-- family needs no `broken … ≡ false`: an api sync has no medium operand, so
-- Task 4's six-field interface weakening does not touch these two facts.  What is
-- NOT true is "the api facts need nothing from the window" — the two corollaries
-- below bind `w` and drop it only because the residual is being carried whole; the
-- HONEST residual is antecedent on the window as well as on `isStable`, and §6e's
-- `-ws` forms are where both antecedents are actually read.  An unread window is
-- a symptom of an over-strong residual, not a finding.
------------------------------------------------------------------------

-- the CONSUME-tail arm at the window-taking shape (the window is bound and not
-- read — see §6e for the form that reads it)
relayOpen-in-w : (l : TwoLegs) (r : RState)
               → Window l (toSys r) (upLink l) (dnLink l)
               → RelayCo l (toSys r) → RefutedAt l lpRelayIn blkA r
relayOpen-in-w l r w = relayOpen-in l r

-- … and the PRODUCE-tail arm
relayOpen-out-w : (l : TwoLegs) (r : RState)
                → Window l (toSys r) (upLink l) (dnLink l)
                → RelayCo l (toSys r) → RefutedAt l lpRelayOut blkA r
relayOpen-out-w l r w = relayOpen-out l r

------------------------------------------------------------------------
-- §6e  *** THE `isStable`-SCOPED FORMS — THE ONLY SHAPE A CONSUMER MAY USE. ***
--
-- `RefutedAt l k b r` is `AtPos l k b (toSys r) → isStable (radec r ∖ hidden
-- blkA) → ⊥` (`LiveStableOffer.agda:1350-1352`), i.e. the consumer HANDS THE
-- PROOF the stability witness.  So the residual need only hold AT STABLE STATES,
-- and stating it there instead of unconditionally is the difference between a
-- refutable premise and a plausibly-true one: §7(a)'s counter-state is a state
-- where a hidden move IS enabled, hence NOT stable, so it does not witness
-- against the scoped form at all.
--
-- The two `-ws` variants scope by the window as well, which is the strongest
-- (weakest-premised) shape available here and the one that finally reads the
-- window §6d binds.  A stable-state obligation also needs NO PRESERVATION
-- CALCULUS — it is discharged per state, not transported along a run — which is
-- the larger half of §7's re-price.
------------------------------------------------------------------------

-- the CONSUME-tail arm, with the residual required only where the consumer asks
relayOpen-in-s : (l : TwoLegs) (r : RState)
               → (isStable (radec r ∖ hidden blkA) → RelayCo l (toSys r))
               → RefutedAt l lpRelayIn blkA r
relayOpen-in-s l r f at sta = relayOpen-in l r (f sta) at sta

-- … and the PRODUCE-tail arm
relayOpen-out-s : (l : TwoLegs) (r : RState)
                → (isStable (radec r ∖ hidden blkA) → RelayCo l (toSys r))
                → RefutedAt l lpRelayOut blkA r
relayOpen-out-s l r f at sta = relayOpen-out l r (f sta) at sta

-- the CONSUME-tail arm, scoped by BOTH the window and stability (the
-- weakest-premised form this module offers, and the one that reads the window)
relayOpen-in-ws : (l : TwoLegs) (r : RState)
                → (Window l (toSys r) (upLink l) (dnLink l)
                   → isStable (radec r ∖ hidden blkA) → RelayCo l (toSys r))
                → Window l (toSys r) (upLink l) (dnLink l)
                → RefutedAt l lpRelayIn blkA r
relayOpen-in-ws l r f w at sta = relayOpen-in l r (f w sta) at sta

-- … and the PRODUCE-tail arm
relayOpen-out-ws : (l : TwoLegs) (r : RState)
                 → (Window l (toSys r) (upLink l) (dnLink l)
                    → isStable (radec r ∖ hidden blkA) → RelayCo l (toSys r))
                 → Window l (toSys r) (upLink l) (dnLink l)
                 → RefutedAt l lpRelayOut blkA r
relayOpen-out-ws l r f w at sta = relayOpen-out l r (f w sta) at sta

------------------------------------------------------------------------
-- §7  *** THE RESIDUAL, PER ARM, WITH ITS PRICE.  READ THIS BEFORE QUOTING
-- `relayOpen-in` / `relayOpen-out` — AND USE §6e's SCOPED FORMS INSTEAD. ***
--
-- `RelayCo` is a REDUCTION TARGET, not a claimed invariant.  Its nine arms do
-- NOT all hold at every reachable state — and that is exactly WHY §6e states the
-- residual under `isStable` rather than unconditionally.  The distinction runs
-- through the whole of this section: an arm may be false as a STATE invariant and
-- still be true at the states the consumer visits, because the states that refute
-- it are states at which some hidden move is enabled, i.e. states that are NOT
-- stable.  Arm by arm:
--
--   · `cp4` (`upClient` at `bcIdle`) — *** FALSE AS A STATE INVARIANT, and that is
--     why the residual is `isStable`-scoped: the counter-state below is a state
--     with an enabled hidden move, so it does NOT witness against §6e's form. ***
--     The counter-state is the LegPos-24 verify report's own machine-checked one
--     (`.superpowers/sdd/2026-08-18-inflightopen-legpos24-spike/spike-verify-report.md`
--     Claim 2(a)): the api sync that moves the relay `cp3 → cp4` IS
--     `apiBF up hi recvBFBlock`, and `bfCnxt (bcAblk b) … recvBFBlock`
--     (`NodeSpecs.agda:552-555`) moves the client `bcAblk b → bcStream`.  So at
--     the ENTRY state of `cp4`, on EVERY path, the client is at `bcStream` and
--     not at `bcIdle`; it reaches `bcIdle` only by reading the server's
--     `MsgBatchDone` (`:548-551`).  The HONEST `cp4` obligation is therefore the
--     TOTAL 7-way dispatch on `NS.BFcPos` the verify report specifies, of which
--     `arm-cp4` above discharges exactly the `bcIdle` arm.  Of the six others:
--     `bcAblk b` is a second-token state (`NoTwoTokens`-shaped, but the banked
--     record has no relay-vs-client field — `LiveLegStep.agda:1306-1313` has
--     four, all server/cell-vs-client); `bcWrr r`/`bcWcd`/`bcBusy`/`bcTerm` are
--     off-region positions needing a relay-phase-to-client-position invariant
--     that does not exist; and `bcStream` is the gate verdict's H22 row
--     (`docs/superpowers/specs/2026-08-11-stable-offer-falsification.md:196`),
--     whose enabled move is NODE A's `apiBF up hi sendBFBatchDone` syncing with
--     A's up BF server at `bsStream` — i.e. it needs `upSrv ≡ bsStream` AND
--     `prodOf ≡ pp6`, plus a node-A four-node lift.  *** `nodes-offer-A` EXISTS
--     NOWHERE IN THE TREE *** — not tracked, and not in either untracked `Spike*`
--     file; `LiveStableOffer` banks `nodes-offer-B` `:1307` and `nodes-offer-C`
--     `:1322` only.  The LegPos-24 verify report's "built in the deleted module in
--     ten lines" is therefore UNREPRODUCIBLE BY CONSTRUCTION, because that stage
--     deleted its own evidence module; treat the figure as an estimate of the
--     OUTER four-node lift alone (`nodes-offer-B` is ~15 lines, so plausible), not
--     of the rung the arm needs.
--   · `cp5` (`upCSc` at `ccIdle`) — plausibly TRUE and unproved.  The relay's own
--     `cp1` fires `apiCS up hi recvCSRollforward`, which returns its CS client to
--     `ccIdle` (`csCnxt (ccArf ht) … ≡ just ccIdle`, `NodeSpecs.agda:361-364`),
--     and nothing but a driver-gated api send leaves `ccIdle` — the gate
--     verdict's §5 says exactly this ("cp5 needs `ccIdle`, true since H11").
--     Proving it needs a driver-phase-to-peer-position invariant over ChainSync.
--   · `cp6`/`pp0`/`pp1`/`pp2` (`dnCSs` at `csAreq`/`csCanAwait`/`csMust`) and
--     `pp3`/`pp4`/`pp5` (`dnSrv` at `bsAreq r`/`bsBusy`/`bsStream`) — the six
--     handshake co-positions of the relay's own DOWN hop.  Each is the position
--     the PREVIOUS sub-phase's own sync leaves the peer in, so each is plausibly
--     true, and each needs the same missing object.
--
-- *** WHAT IS MISSING, AND WHAT IT COSTS — the finding this task reports. ***
-- Five of the nine arms name a CHAINSYNC peer position, and the claim to make
-- about that is a precise one:
--
--   *** NO PROVED INVARIANT in this development constrains a ChainSync position.
--   The only per-state predicates that do are this module's own `CoAt` (§6b) and
--   the LegPos-24 spike's `SpikeAtPos` — which was green, with five CS conjuncts,
--   but DEFINED AND CONSUMED, NEVER ESTABLISHED (no base case, no step, no
--   reachability, and its reverse map `legInv⇒spikeBare` landed WITHOUT the CS
--   conjuncts).  That spike was untracked throughout and was DELETED at the
--   campaign close; its content is recorded in the campaign's task-4 report. ***
--
-- Verified over ALL of `src/`, not a sub-scope: `CScPos`/`CSsPos` occurs on ~573
-- lines in ~47 files, of which ~350 sit in `R2_Bisim/`; inside `LTL/` and
-- `CSP_Refinement/` the occupants are `PipeBundleEvo`, `PipeBundleIoEvo`,
-- `PipeBundleRecv`, `PipeNodeIoEvo`, `PipeSrvFire`, `PipeVal*`, the FIVE
-- `WalkConv*` cones (`NodeDrop`, `IoDrop`, `Measure`, `NodeWt`, `NodeFix`),
-- `LiveLegApiCone`, `LiveLegIoCone`, `LiveIoIntro`, `LiveRetFree`,
-- `LiveStableOffer`, `LiveKAFrozen`, the two (now deleted) `Spike*` files — and
-- THIS MODULE (12 hits).  What is ChainSync-CLEAN is every PROVED invariant: `LiveLegInv.LegInv`,
-- `PipeInv.PipeInv`/`PipeInv⁺`, `PipeInvProd.PipeInvS`,
-- `LiveLegStep.NoTwoTokens`, `LiveTokenExcl.TokenExcl`, and
-- `LiveChanInv.ChanInv`, whose three places are instantiated purely through
-- `coarsenBFs`/`coarsenBFc`.  So closing the api family needs, at minimum:
--
--   (a) a CHAINSYNC per-hop channel invariant — the exact analogue of
--       `LiveChanInv`'s five clauses on `(BFsPos, CopyPhase, BFcPos)`, over
--       `(CSsPos, CopyPhase, CScPos)`, whose tables are LARGER (`csSnxt`
--       `NodeSpecs.agda:414-490`, `csCnxt` `:304-381`; 13 × 12 positions against
--       BlockFetch's 10 × 7, table bulk 155 lines against 97) — plus its
--       adjacency transcriptions, its preservation calculus and its leg lift.
--       Comparable, COUNTED AS CODE (not raw insertions): `LiveChanInv` 888 +
--       `LiveChanRead` 118 + the T2b wiring 548 = 1,554.
--   (b) DRIVER-to-PEER co-position invariants, which the campaign has never
--       needed before: `PipeInv.Coupled` `:483-488` and `PipeSrvInv.SrvCoupled`
--       `:77-81` both run OCCUPANCY ⇒ driver-phase-region, the opposite
--       direction, and `LiveTokenExcl.UpChainCp3`/`DnChainCp3` (`:256-262`) are
--       unproved PARKED premises and also occupancy-antecedent.  Under §6e's
--       scoped shape these are THREE OR FOUR table-shaped predicates, one per
--       (protocol, hop), each paying preservation ONCE the way `ChanInv` does —
--       not nine independent invariants, and the arms that can exhibit an enabled
--       move need none at all.
--   (c) the CHAINSYNC io ladders: every ladder T2c banked (`medOfferIn`,
--       `medOfferOut`, `medDrainτ`, `srvInNodes-*`) is keyed at
--       `N2N_BlockFetch`, and the `cp5`/`cp6`/`pp0..pp2` tails run through
--       `N2N_ChainSync` cells and CS peers.  Comparable: T2c's 726 INSERTIONS are
--       475 code, and the named definitions themselves 259.
--   (d) the H22 node-A ladder of the `cp4` arm above.  `nodes-offer-A` exists
--       nowhere (see the `cp4` bullet); the outer four-node lift is
--       `nodes-offer-B`-sized (~15 lines) off
--       `SysRoute.absNode{B,C,D}-no-when-A` `:2042-2049`/`:2051-2058`/`:2060-2064`,
--       and the real cost is the node-A-INTERNAL lift, whose DRIVER operand is
--       itself a `⦀` of A's two producers (`SysStep.agda:761-765`) — a
--       sibling-PRODUCER non-offer this development does not bank, the banked
--       `absNode*-no-when-A` family being about WHOLE NODES.  The same two-driver
--       hazard exists at node D (`absNodeD`, `SysStep.agda:779-783`); node B and
--       node C are the easy ones, their driver operand being a single `decCP`
--       (`:767-771`, `:773-777`).
--   (e) a fifth `NoTwoTokens` field (relay-vs-client) and its preservation:
--       `LiveLegStep.agda:1306-1313` has four, each pairing a slot against the BF
--       client immediately downstream; the only widening,
--       `LiveTokenExcl.TokenExcl :283-292`, adds `nUpSrvCell`/`nDnSrvCell` and
--       still has no relay-vs-client field.
--
-- On the campaign's own measured densities that is ≈2,000-4,500 code lines
-- (bands: (a) 1,100-2,200, (b) 400-1,200, (c) 250-550, (d) 100-300, (e)
-- 100-250), not the ≈650-1,000 this task was priced at, and even the low end is
-- about twice the remaining cap headroom of 1,057 (campaign code ≈2,793 + this
-- module's 650 = 3,443 against a 4,500 cap).
--
-- *** THE HISTORY OF THE UNDER-PRICE, for the record, because two earlier
-- accounts of it are wrong. ***  The gate verdict UNDER-DIAGNOSED: its §5
-- (`docs/superpowers/specs/2026-08-11-stable-offer-falsification.md:242`) covers
-- `cp4`/`cp5`/`cp6` only — three of the nine — absorbs the produce tail
-- `pp0..pp5` into "the down hop's H0-H20 (all τ)" rather than diagnosing six api
-- obligations, and gets `cp6` WRONG (this module's `relay-offer-cp6` refutes the
-- "`cp6` → `sil` bind hop" reading).  The LegPos-24 verify report then WIDENED the
-- enumeration CORRECTLY — its `:164-167` gives all nine sub-phases across all four
-- co-party classes with exact cardinalities (7/12/13/10, ≤101 arms per leg) — and
-- correctly refuted the client pin; what it did only for `cp4` was the PRUNING and
-- the PRICING.  The actual under-price is a DENSITY TRANSPLANT: the ≈4.77
-- lines/clause figure was measured on total decode/step TABLES, where a clause is
-- one line because it RETURNS A VALUE, and was applied to unreachability ARMS,
-- which must derive `⊥` — and deriving `⊥` needs either an enabled move (a
-- ladder) or an invariant.  The verify report's own five pruned `cp4` arms are
-- prose reachability arguments with no formal carrier.  So: gate under-diagnosed
-- (3 of 9, one of the 3 wrong) → verify report widened the enumeration correctly
-- but transplanted a table density onto proof obligations → this task re-priced
-- correctly.  `cp4` remains the one sub-phase of nine whose co-party is a
-- BlockFetch peer, i.e. the only one the banked invariant vocabulary can talk
-- about, which is why pricing it alone under-prices the family. ***
------------------------------------------------------------------------

------------------------------------------------------------------------
-- FALSIFICATION NOTES (arity-preserving mutations, applied, built and reverted
-- byte-identically; `git status --short` back to exactly the pre-existing
-- untracked files after each).  ONE PER PROOF LAYER, as the campaign rule asks:
-- the peer offer, the sync kit's operand side, the driver offer's link, the
-- position dispatch, the vacuity mode of the co-position dispatch, and — added in
-- the fix round — the `isStable` scoping of §6e.
--
-- (F1  the PEER OFFER, `arm-cp4` at leg BD)  feed `peer-cp4` node B's DOWN-link
--      BF client slot (`bfC-BD`) in place of its up-link one (`bfC-AB`).
--      *** RED as predicted ***, and with a SHARPER error than predicted:
--      `:625.9-69: error: [MismatchedProjectionsError] The projections
--      NodeStateB.bfC-BD and NodeStateB.bfC-AB do not match`, EXIT=42 — a
--      projection mismatch rather than an `[UnequalTerms]`, because both sides are
--      record projections of the SAME node state.  So the arm genuinely reads
--      the leg's UP-hop client slot — the component the `cp4` co-position names —
--      and not the other bundle's client, which is the mis-slot a hand-written
--      seventeen-position dispatch is most likely to introduce.
--
-- (F2  the SYNC KIT, `syncDn-BD`)  the node-B bundle lift `⦀-ev-R` → `⦀-ev-L`.
--      *** RED as predicted ***: `:517.25-30: error: [UnequalTerms]
--      (Fin.suc (fromℕ< _)) != Fin.zero of type (Fin (Params.numLinks p)) … when
--      checking that the expression bstep has type absBundleG linkAB hi lo …`,
--      EXIT=42.  So the LEG↔OPERAND mapping inside the relay
--      node is load-bearing in BOTH directions: leg BD's UP link is node B's LEFT
--      bundle (the mutation `LiveStableOffer`'s M1 measured) and its DOWN link the
--      RIGHT one (this one).
--
-- (F3  the DRIVER OFFER, `relay-offer-cp4`)  offer the driver's event on `l₂`
--      (the DOWN link) instead of `l₁` (the up link).
--      *** RED as predicted ***: `:352.19-35: error: [UnequalTerms] l₂ != l₁ of
--      type Fin (Params.numLinks p) … when checking that the expression
--      consVis-cp4 l₂ b has type Output-cont … (apiBF l₁ hi sendBFClientDone) …`,
--      EXIT=42.  So which of the relay's two links each
--      sub-phase drives is load-bearing — the `cp4..cp6` tail drives the UP link
--      and the `pp0..pp5` tail the DOWN one, and the `cp6`/`pp0` collapse is the
--      one place they meet.
--
-- (F4  the DISPATCH, `relayOpen-in`)  route the `cp5` disjunct to `arm-cp4`.
--      *** RED as predicted ***: `:920.50-52: error: [UnequalTerms] cp5 != cp4 of
--      type ConsPh … when checking that the expression eq has type relayOf l
--      (toSys r) ≡ consuming (relayBlk (relayOf l (toSys r))) cp4`, EXIT=42.  So
--      the nine same-SHAPED arms cannot be cross-wired: each
--      sub-phase's own phase equation catches a mis-route, which is the guard that
--      matters most in a dispatch whose arms are nine copies of one interface.
--
-- (F5  THE VACUITY MODE — the mutation that tests §6b's totality)  replace
--      `CoAt`'s `producing _ pp5` clause by `⊤`.
--      *** RED as predicted ***: `:950.54-84: error: [UnequalTerms] Level.Lift
--      Level.zero U.⊤ !=< coarsenBFs (dnSrv l (toSys r)) ≡ NS.bsStream … when
--      checking that the expression subst (CoAt l (toSys r)) eq co has type
--      coarsenBFs (dnSrv l (toSys r)) ≡ NS.bsStream`, EXIT=42.  So a silently-`⊤`
--      arm of the co-position dispatch is a type error at its consumer rather than
--      a weaker theorem — which is the property that makes `CoAt` a faithful
--      statement of the residual and not a container for it.
--
-- (F6  THE `isStable` SCOPE of the fix round, `relayOpen-in-s`)  feed the scoped
--      residual the POSITION (`f at`) in place of the STABILITY WITNESS (`f sta`)
--      — same arity, both arguments in scope.
--      *** RED as predicted ***: `:1025.51-53: error: [UnequalTerms] (Σ (RelayIn⁺
--      blkA blkA (relayOf l (toSys r))) (λ x → ProdSent … × InCp03 …)) !=<
--      (isStable (radec r ∖ hidden blkA)) … when checking that the expression at
--      has type isStable (radec r ∖ hidden blkA)`, EXIT=42.  So §6e's scoping is
--      load-bearing: the residual is discharged AT THE STABILITY WITNESS the
--      consumer hands over, and nothing else in scope can stand in for it.  This
--      is the mutation that distinguishes the scoped form from the bare one — the
--      bare `relayOpen-in` cannot be tested this way at all, which is precisely
--      the review's point.
------------------------------------------------------------------------

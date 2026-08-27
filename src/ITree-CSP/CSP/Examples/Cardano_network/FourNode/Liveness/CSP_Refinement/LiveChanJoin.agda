{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `LiveChanJoin` — *** THE CHANNEL INVARIANT, JOINED TO THE CARRIED FOLD. ***
--
-- `LiveChanInv` proves the per-hop BlockFetch channel invariant's base, frame and
-- preservation across every step class; what it does NOT do is thread it along a
-- run.  That is this module: the assembly's `LegJoint⁺` gains a TRAILING factor
-- and each of `LiveLegAssembly` §9's five arms gains the matching half, so the
-- FSim's `Rel` carries the invariant instead of premising it.
--
-- *** WHY A NEW MODULE AND NOT `LiveLegAssembly` ITSELF. ***  `LiveChanInv` sits
-- ABOVE the assembly (it imports `LiveStableOffer`, which imports
-- `LiveLegAssembly`), so `ChanUp` is not even in scope down there.  Joining
-- therefore happens HERE, one level up, in the shape the fold's own genericity
-- already supports: every arm CALLS the assembly's arm at the SAME arguments — so
-- the successor is literally the same term, no second peel, no F2 pairing problem —
-- and adds the channel half beside it.
--
-- *** WHAT IS JOINED (read this before quoting). ***  BOTH hops.  The leg's whole
-- `LiveChanInv.ChanLeg` — `ChanUp × ChanDn` — is carried across ALL FIVE step
-- classes, so all EIGHT of `LivenessProof`'s io-side in-flight facts are
-- PREMISE-FREE theorems (they still carry the `InFlightOpen` field's own
-- link-unbrokenness antecedent, which is intrinsic to that field type since task
-- 1's weakening).  `Premises` retains no channel field at all.
--
-- *** THE ARMS ARE HOP-PARAMETRIC, NOT DUPLICATED (task-4b review (iii)). ***  §4's
-- `module HopArm` abstracts over the hop's four accessors and its cell-key bridge,
-- and §5 instantiates it TWICE (`HUp` at `upLink`/`upSrv`/`upClient`/`cellUp`, `HDn`
-- at the `dn*` quartet).  `LiveChanInv` is already hop-generic underneath —
-- `ChanUp`/`ChanDn` are both `ChanInv` instances and both `-pres` lemmas are
-- one-liners off `chanInv-pres-eq` — so nothing below needs a second copy: in
-- particular the api arm's twenty-one-clause label dispatch and the four
-- row-refutation tables exist ONCE and serve both hops.  A third hop would cost an
-- instantiation line.
--
-- *** WHAT UNBLOCKED THE DOWN HOP, AND WHY IT NEEDED NO GRANT. ***  The down hop's
-- client is NODE D's, and node D's api peel used to be the frozen
-- `PipeEvDriverCone.NodeDDrv`, which reports only `(fixed) ⊎ (¬holding successor)`
-- about the very client it moves — no fired row, no successor identity — while a
-- second peel of node D's step cannot be tied to the frozen one (`absNodeD` is not
-- injective).  The obstruction sat one layer deeper still: `NodeDDrv`'s client slot
-- is fed verbatim from `PipeBundleEvo.BundleGEvR⁺`'s own client slot (`bgEB⁺`,
-- `:940-946`, the client slot `:944`), a datatype matched at 28 sites across three modules
-- (`PipeBundleEvo` 14, `PipeEvDriverCone` 8, `PipeNodeAEvo` 6); its SERVER slot
-- already carries `BfsSucc`, so the CLIENT slot alone was the gap.  Rather than
-- widen that datatype (a base edit), `LiveLegApiExpose` §8 re-mirrors node D's api
-- peel in the CSP layer, calling the already-landed
-- `PipeBundleEvo.decBFc-apiBF-succ-row⁺` through §4's `absBundleG-api-evo⁺` and
-- bypassing `BundleGEvR⁺` entirely — exactly what that module's own `bfEvRio→api`
-- chain already did for the UP hops.  `driverExpose⁺` then reports the two DOWN-hop
-- row pairs beside the two UP-hop ones.
--
-- No postulate/hole/meta/`mutual`/`NON_TERMINATING`; every arm is a single-clause
-- `let`-only definition, as §9's convertibility finding requires.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
-- (T8c-iii) §5f transports the relay's successor equation into the guard
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong; subst )
open import Relation.Nullary using ( yes; no )
open import Class.DecEq using ( DecEq; _≟_ )
import Class.DecEq.Instances as DecEqI

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanJoin
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; break; apiBF; apiCS; apiKA; apiTS; apiLN; apiLF
  ; done; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack
  ; ApiBFTag; ApiBFCar )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; hi; IDs; N2N_BlockFetch; N2N_ChainSync; N2N_KeepAlive; N2N_TxSubmission
  ; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; empty; full; draining; phase; decMed; MedState; mkMed; broken )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absNodesOf; coarsenBFs; coarsenBFc
        -- (T8c-iii) §5e's frame coarsens node D's client slot for the coupling, and
        -- §5g's io arms coarsen both CS peers for the row→adjacency lemmas
        ; coarsenCSc; coarsenCSs
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( absNodesOf-no-τ )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( oevB-no-io; oevB-refute )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  -- (T8c-iii) §5f's relay branch refutes the dn CS server's row BY LINK
  using ( aicCS; aicBF; aicDone; ApiHasLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( IsApiCSBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( phase-upd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell )
-- the payload's ROLE: every wire payload is client- or server-originated, which is
-- what makes the "neither peer moved" case of an io FILL refutable
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( ClientIo; ServerIo; msgOrigin )
open import CSP.Examples.Cardano_network.Data p using ( Messages )
open import CSP.Examples.Cardano_network.Base using ( Mode; FromInitiator; FromResponder )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeIoEvo blkA
  using ( NoCliIoAt; NoSrvIoAt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD
        -- (T8c-iii) node D's phase and stored block, leg-stated
        ; phOf; cblkOf
        -- (C, cellCp3) … and node D's PRE-RECEIVE region, the dn-hop twin of
        -- `RelayPre` that §5e's down-hop position lemma partitions
        ; InCp03 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
-- the two hops' peer/cell/link accessors: §4's `HopArm` is parametric in the
-- QUARTET, and §5 instantiates it at each
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( cellUp; upClient; cellDn; dnClient
        -- (T1) the relay driver's own phase — S1's antecedent slot
        ; relayOf
        -- (T10) … and node A's, which the eighth factor's frame reads, and the
        -- client's block occupancy, which its api premise reads
        ; prodOf; BFcHasBlk; ProdSent
        -- (T11e) … and the TOKEN itself, which §6h's record's api class projects
        -- `InCp03` out of per state (review C-1) rather than carrying it
        ; PipeInv
        -- (C, cellCp3) … and the relay's PRE-RECEIVE region, which §5e's up-hop
        -- position lemma partitions into slice A's guard and the window's conclusion
        ; RelayPre )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauMed blkA
  -- (T8c-iii) §5f's `up≢dn` is the leg's own two-link disequality
  using ( drainSucc; linkAB≢linkBD; linkAC≢linkCD )
-- (T8c-iii) node D's driver advance, at the pair the merged cone field carries
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ConsAdv )
-- the fine BF peer positions the four accessors return
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  -- (T8c-iii) §5f states node D's driver step at `consD (cblkOf l s) (phOf l s)`, which
  -- is the leg-stated form of the cone's node-projection one (η on `ConsDPh`)
  using ( BFsPos; BFcPos; consD; decConsD; cph; NodeStateD
        ; ProdPh; producing; pp0; ConsPh; consuming
        -- (T11e) the guard region's two sub-phases, which S6h's api arm dispatches on,
        -- and node D's own `cp3`, which the BF fold's anchor is conditional on
        ; pp2; pp3; cp3
        -- (C, cellCp3) … and the relay's own phase datatype with its remaining six
        -- sub-phases: §5e's two position lemmas are TOTAL dispatches over them
        ; CPPh; cp0; cp1; cp2; cp4; cp5; cp6 )
-- the leg's own cell key, propositionally: `cellUp l s` is `phase (med s) (upLink l)
-- hi N2N_BlockFetch` only after the leg is a constructor, so every hop-level
-- statement about the medium goes through this (and the `dn` twin, for the down hop)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauIo blkA
  using ( cellUp-key; cellDn-key )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeMedKey blkA
  using ( medium-ev-in-key; medium-ev-out-key )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiExpose blkA
  using ( driverExpose⁺
        -- (T8c-iii) the two MERGED node-D fields and the two relay ones
        ; deNodeDBD; deNodeDCD; deRelayBD; deRelayCD; deRelayAdvBD; deRelayAdvCD
        -- (T3b) the cone's report is a RECORD; these are the slots this module reads
        ; deSucc; deMed; deRowsAB; deRowsAC; deRowsBD; deRowsCD; deDnDrvBD; deDnDrvCD
        -- (T5) the two legs' CS-server pairs
        ; deCsDrvBD; deCsDrvCD
        -- (T6c, grant #12) … and the two api slots the CS join needs beside them:
        -- node A's UP-hop CS SERVERS and node D's DOWN-hop CS CLIENTS
        ; deCSRowsBD; deCSRowsCD; deCSUpSrvBD; deCSUpSrvCD; deCSDnCliBD; deCSDnCliCD
        -- (T7) … and the two legs' UP-hop CS-CLIENT chains, the `cp5` arm's own
        ; deUpCsDrvBD; deUpCsDrvCD
        -- (T10) … and the four slots the EIGHTH factor reads: the two legs' driver
        -- steps, their leaf records, and the two (T10) up-hop BF-CLIENT pairs
        ; deLdBD; deLdCD; deVlBD; deVlCD; deUpBfBD; deUpBfCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone blkA
  using ( top-nodes-io-evoP⁺ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvStep blkA
  using ( break-invert )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( PipeVal )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveKAFrozen blkA
  using ( KAcFrz )
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegStep blkA as LS
-- (T10) §5i's cell predicate (the `full`-only one the token's own chains use)
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA as LLI
-- (T10) … and the token exclusion, whose `NoTwoTokens` field the eighth factor's api
-- premise reads off the join's first factor
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveTokenExcl blkA as LTE
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegAssembly blkA as LA
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone blkA as LIC
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiCone blkA as LAC
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanInv blkA as LCI
-- (T1) S1, the BlockFetch DRIVER-TAIL coupling — the campaign's shared BF object,
-- joined below as the FIFTH trailing factor
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBF blkA as LDB
-- (T6c) the ChainSync channel invariant and its hop-parametric join arms — the SIXTH
-- trailing factor and the five arms that carry it
-- (T11e) the coarse BF-client positions the fold's anchor names, and (T11g) the FIFTH
-- factor's own third half — `BFFresh`, folded into `DrvBF` (§5c⁺)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBFD blkA as LBFD
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanCS blkA as LCC
-- (T6c) the CS api-axis facts, for §5d's two typed leg dispatches
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCSRow blkA
  using ( CSsApiRowP; CScApiRowP )
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanJoinCS blkA as LCJC
-- (T8c-iii) node D's freshness clause and its driver-tail coupling, carried as
-- `LegJointU`'s SEVENTH factor.  This is the edge that brings `LiveDrvCSD` into the
-- endpoint's closure for the first time
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvCSD blkA as LDC
-- (T10) node A's up-hop BF coupling and the `cp4` client region — the EIGHTH factor,
-- travelling as ONE pair for `DnJoint`'s reason
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBFA blkA as LDBA
-- (T5) the down-hop CS SERVER slot accessor, for the new io selector's TYPE (the
-- coupling's own third component is stated at it, so the two must be the same term)
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveRelayOpen blkA
  -- (T7) … and the leg's UP-hop CS CLIENT slot, which the `cp5` chain's selectors are
  -- stated at for `dnCssRow`'s reason: the leg being a CONSTRUCTOR is what makes the
  -- cone's node-field form and the coupling's `upCSc` form convertible
  using ( dnCSs; upCSc )

------------------------------------------------------------------------
-- §1  THE JOINED INVARIANT.
------------------------------------------------------------------------

-- the assembly's joint invariant WITH the leg's WHOLE channel invariant (both
-- hops), per leg.
-- *** THE FACTOR IS TRAILING INSIDE THE ASSEMBLY'S OWN PRODUCT, not wrapped around
-- it: *** `LegJoint⁺` is `LegJoint × PipeVal × KAcFrz`, so appending keeps every
-- `proj₁`-rooted access in the existing consumers (`LiveFSim`'s twenty-odd reads of
-- `PipeInvS`, `LegInv`, `TokenExcl` and `PipeVal`) BYTE-IDENTICAL.  Wrapping instead
-- costs one `proj₁` at every one of them (measured: `[UnequalTerms] … !=
-- SrvCoupled legBD (toSys r)` at the first).  Widening the factor from `ChanUp` to
-- `ChanLeg` (task 5) keeps that property too — `ChanLeg` is itself a product, so
-- only the two channel READERS below moved, and `LiveFSim`'s CODE did not change at
-- all (its comments did, at the close; only `LiveRetFree` is literally byte-identical
-- across task 5 — final-review M-1).
-- *** (T1) AND THE FIFTH FACTOR IS S1, appended by the same discipline. ***  The
-- BlockFetch driver-tail coupling (`LiveDrvBF.DrvBF`) joins as a further TRAILING
-- factor, so every `proj₁`-rooted access in every existing consumer stays
-- byte-identical again; only the two channel READERS below moved (they now have to
-- reach INSIDE the fourth factor), exactly as widening `ChanUp` to `ChanLeg` moved
-- them at task 5.  T2's `pp5` arm and T8's `cp4` arm are FIELDS of that record, so
-- they cost nothing here at all.
-- *** (T7) THAT LAST SENTENCE IS TRUE ONLY OF A CHANGED FIELD TYPE, AND T7 IS THE
-- COUNTEREXAMPLE — READ THIS BEFORE PRICING ANY FURTHER ARM OFF THIS MODULE. ***  Three
-- consecutive arms cost this file ZERO edits (T2's `pp5`, T5's `pp1`, T6d's `pp2`) and the
-- review chain accordingly banked "`LiveChanJoin` costs nothing".  **It does not.**  T7's
-- `cp5` cost **16 net**, and the cost model that actually holds is per INGREDIENT:
--
--   · a changed field TYPE inside an existing record slot — **ZERO**.  The leg dispatches
--     below (`drvDn`/`csDrv`/`upCsDrv`) are `_`-typed, so they adapt to a widened field
--     without an edit; that is what made T2/T5/T6d free, and it is a real property of the
--     design rather than luck.
--   · a NEW `DriverExposed⁺` FIELD — **not free.**  `deUpCsDrvBD`/`deUpCsDrvCD` need a
--     `using`-list entry (T7's ONE red round was exactly this omission), a `let` binding
--     at the api arm, a new `_`-typed leg dispatch and one call-site argument.
--   · a NEW io PREMISE on one of `LiveDrvBF`'s five class arms — **not free.**  `cp5`'s
--     up-hop client fact needed a new typed selector (`upCscRow`) plus a call-site
--     argument in BOTH io classes; a `_`-typed selector cannot serve here, because the
--     selector COMBINES cone slots rather than returning one of its own arguments (the
--     `csApiUp` note in §5d gives the measured reason).
--   · a new FRAME component — one argument per frame call site (`upCSc-fix`, two sites).
--
-- *** Price the next arm per ingredient, not per arm, and do not quote the three zeros. ***
-- *** (T6c) AND THE SIXTH FACTOR IS THE CHAINSYNC CHANNEL INVARIANT, appended by
-- the same discipline. ***  `LiveChanCS.ChanCSLeg` — both CS hops of the leg — joins
-- as a further TRAILING factor, so every `proj₁`-rooted access in every existing
-- consumer stays byte-identical once more; only `drvBF-of` moves (it now has to end
-- in a trailing `_`, exactly as the two channel readers moved when `DrvBF` was
-- appended at T1).  `pp2`'s arm reads it through `chanCSLeg-of`.
LegJointU : TwoLegs → SysState → Set
-- (T8c-iii) … and `LiveDrvCSD.DnJoint` — node D's freshness clause paired with its
-- driver-tail coupling — joins as the SEVENTH trailing factor, so once more every
-- `proj₁`-rooted access stays byte-identical and only `chanCSLeg-of` moves.  The pair
-- travels as ONE factor because every step class that moves one moves the other; that
-- halves the arm plumbing (five arms × one argument, not two)
-- (T10) … and `LiveDrvBFA.UpJoint` — node A's up-hop BF coupling paired with the
-- `cp4` client region — joins as the EIGHTH trailing factor, so once more every
-- `proj₁`-rooted access stays byte-identical and only `dnJoint-of` moves.  The pair
-- travels as ONE factor for the seventh's reason exactly
-- (T11h) … and the FIFTH factor is now the PAIR `LiveDrvBFD.BFJoint` — `DrvBF` with
-- the down hop's BF FRESHNESS clause folded in.  A FOLD and not a ninth factor: the two
-- halves walk the SAME down-BlockFetch hop, so each of the five arm sites below carries
-- ONE extra component instead of a whole arm set (`LiveDrvBFD` §3's measurement).  Every
-- `proj₁`-rooted access is untouched, and only `drvBF-of` moves — it now projects
LegJointU l s = LA.LegJoint l s × PipeVal l s × KAcFrz s × LCI.ChanLeg l s
                  × LBFD.BFJoint l s × LCC.ChanCSLeg l s × LDC.DnJoint l s
                  × LDBA.UpJoint l s

-- … and both legs at once, in the ∀-form the FSim's `Rel` carries (the leg index is
-- vestigial, exactly as in `LA.LegJointB`)
LegJointUB : TwoLegs → SysState → Set
LegJointUB _ s = (l : TwoLegs) → LegJointU l s

-- BASE: the assembly's base beside the channel invariant's own (both hops)
legJointUB-init : (l : TwoLegs) → LegJointUB l initial
legJointUB-init _ l =
  let (j , pv , frz) = LA.legJointB-init legBD l
  in  j , pv , frz , LCI.chanLeg-init l , LBFD.bfJoint-init l , LCC.chanCSLeg-init l
    , LDC.dnJoint-init l , LDBA.upJoint-init l

-- the assembly's own product, re-assembled (what its arms and every existing
-- consumer take)
legJoint⁺-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LA.LegJoint⁺ l s
legJoint⁺-of l s (j , pv , frz , _) = j , pv , frz

-- … and at both legs
legJointB-of : (s : SysState) → LegJointUB legBD s → LA.LegJointB legBD s
legJointB-of s f l = legJoint⁺-of l s (f l)

-- glue the assembly's product, the channel half and (T1) the driver-tail coupling
-- into the joined one
mkU : (l : TwoLegs) (s : SysState) → LA.LegJoint⁺ l s → LCI.ChanLeg l s
    → LBFD.BFJoint l s → LCC.ChanCSLeg l s → LDC.DnJoint l s → LDBA.UpJoint l s
    → LegJointU l s
mkU l s (j , pv , frz) iv db cs dn up = j , pv , frz , iv , db , cs , dn , up

-- the channel half, whole …
chanLeg-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LCI.ChanLeg l s
chanLeg-of l s (_ , _ , _ , iv , _) = iv

-- … and its two hops (the extra parentheses are (T1)'s only consumer churn: the
-- fourth factor is no longer the LAST, so `ivU`/`ivD` sit one level in)
chanUp-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LCI.ChanUp l s
chanUp-of l s (_ , _ , _ , (ivU , _) , _) = ivU

chanDn-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LCI.ChanDn l s
chanDn-of l s (_ , _ , _ , (_ , ivD) , _) = ivD

-- (T1) … and S1 itself, the fifth factor
-- (T6c) … the fifth factor, which is no longer the LAST — the ONE reader the sixth
-- append moves, exactly as (T1)'s append moved the two channel readers
-- (T11h) … and the fifth factor is now a PAIR, so this reader PROJECTS.  Every other
-- consumer of `DrvBF` in the endpoint's closure reads it through here, which is what
-- makes the fold cost one line at the interface
drvBF-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LDB.DrvBF l s
drvBF-of l s (_ , _ , _ , _ , db , _) = LBFD.bfJoint⇒drv l s db

-- (T11h) … the fifth factor WHOLE, which the five arm sites take and rebuild
bfJoint-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LBFD.BFJoint l s
bfJoint-of l s (_ , _ , _ , _ , db , _) = db

-- … and its second half alone
bfFresh-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LBFD.BFFresh l s
bfFresh-of l s (_ , _ , _ , _ , db , _) = LBFD.bfJoint⇒fresh l s db

-- (T6c) … and the SIXTH factor itself, the leg's two ChainSync hops
chanCSLeg-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LCC.ChanCSLeg l s
chanCSLeg-of l s (_ , _ , _ , _ , _ , cs , _) = cs

-- (T8c-iii) … and the SEVENTH factor itself — node D's pair
dnJoint-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LDC.DnJoint l s
dnJoint-of l s (_ , _ , _ , _ , _ , _ , dn , _) = dn

-- (T10) … and the EIGHTH factor itself — the up hop's pair
upJoint-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LDBA.UpJoint l s
upJoint-of l s (_ , _ , _ , _ , _ , _ , _ , up) = up

-- … at both legs, in the ∀-form `LivenessProof.ifo-of` holds
upJointB-of : (s : SysState) → LegJointUB legBD s → (l : TwoLegs) → LDBA.UpJoint l s
upJointB-of s f l = upJoint-of l s (f l)

-- (T1) … at both legs, in the ∀-form `LivenessProof.ifo-of` holds
drvBFB-of : (s : SysState) → LegJointUB legBD s → (l : TwoLegs) → LDB.DrvBF l s
drvBFB-of s f l = drvBF-of l s (f l)

------------------------------------------------------------------------
-- §2  THE HOP-FREE BRICKS.  Everything below this heading is stated at ABSTRACT
-- keys and positions, so it is shared by both hops with no instantiation at all:
-- the medium's two key dichotomies, the payload's ROLE, the two ownership
-- refutations and the four row-refutation tables.
------------------------------------------------------------------------

-- *** KEEP IN SYNC WITH `LTL/Value/PipeTauMed.cell-drain-eq` (`:98-107`), PART BY
-- PART. ***  Both anchors re-derived by grep at the task-4b fix round.
--
--   · `:98-101`  the SIGNATURE — transcribed with two deviations, both deliberate:
--                (a) the statement is at the SYSTEM level (`s : SysState` and
--                    `phase (med (drainSucc s i d₀ id₀))`) rather than at
--                    `MedState` with the raw `phase-upd … flipCell` term, because
--                    every caller here holds a `SysState`;
--                (b) the HIT arm reports all THREE key equations
--                    (`kl ≡ i` × `kd ≡ d₀` × `kid ≡ id₀`), where the banked one
--                    reports `kl ≡ i` only.  That is the whole reason this variant
--                    exists: without `kd`/`kid` the source phase cannot be
--                    identified with the drain inversion's `draining x`.
--   · `:102-107` the four CLAUSES — transcribed line for line (same `with kl ≟ i`,
--                then `kd ≟ d₀ | kid ≟ id₀`), only the payloads widened to match
--                the deviation above.
--
-- Both deviations are in the safe direction (more informative output at a more
-- concrete state); a re-sync must preserve them, not "restore" the banked shapes.
-- If `cell-drain-eq`'s CASE STRUCTURE changes, this one rots silently.

-- the drain's effect at ONE key: untouched, or this IS the drained key
drain-cell-at : (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                (kl : Link) (kd : Dir) (kid : IDs)
  → (phase (med (drainSucc s i d₀ id₀)) kl kd kid ≡ phase (med s) kl kd kid)
    ⊎ ((kl ≡ i) × (kd ≡ d₀) × (kid ≡ id₀)
       × (phase (med (drainSucc s i d₀ id₀)) kl kd kid ≡ empty))
drain-cell-at s i d₀ id₀ kl kd kid with kl ≟ i
... | no  _ = inj₁ refl
... | yes refl with kd ≟ d₀ | kid ≟ id₀
...   | yes refl | yes refl = inj₂ (refl , refl , refl , refl)
...   | no  _    | _        = inj₁ refl
...   | yes refl | no  _    = inj₁ refl

-- *** THE ONE MEDIUM BRICK. ***  `PipeMedKey.setRead` already decides an arbitrary
-- cell key against the fired one and hands back the new phase; what it does NOT hand
-- back is the MISS's REASON, and the io arms need exactly that — it is what refutes a
-- peer's fired ROW away from the hop's key.  So this is `setRead`'s own proof with the
-- disequality kept.  Proving it HERE, at abstract keys, is also what makes it work at
-- all: inside the definition every comparison is on a variable, whereas a caller that
-- unifies the keys first is left with FRESH stuck comparisons no `with` reaches
-- (measured twice: `… | upLink l ≟ upLink l …` and `(upLink l) != (upLink l) …
-- because one is a variable and one a defined identifier`).
--
-- *** KEEP IN SYNC WITH `LTL/Value/PipeMedKey.setRead` (`:368-380`), PART BY PART. ***
-- Anchors re-derived by grep at the task-4b fix round.
--
--   · `:368-372` the SIGNATURE — transcribed verbatim except for ONE deliberate
--                deviation: the MISS arm is a PAIR, its first component the miss's
--                REASON as the three-way `(kl ≡ i → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎
--                (kid ≡ id₀ → ⊥)`.  The frame equation itself, its orientation
--                (`g kl kd kid ≡ phase-upd …`) and the whole HIT arm are identical.
--   · `:373-380` the four CLAUSES — same case structure (`with kl ≟ i`, then
--                `kd ≟ d₀ | kid ≟ id₀`), same four outcomes; each `inj₁ refl`
--                becomes `inj₁ (<that branch's reason> , refl)`.
--
-- The deviation is in the safe direction (strictly more informative output), and it
-- is load-bearing: `srvRow-off`/`cliRow-off` below consume exactly that reason.  A
-- re-sync must preserve it, not "restore" `setRead`'s bare `inj₁ refl`s; and if
-- `setRead`'s CASE STRUCTURE changes, this variant rots silently.
setRead⁺ : (g : Link → Dir → IDs → CopyPhase) (i : Link) (d₀ : Dir) (id₀ : IDs)
           (np : CopyPhase) (kl : Link) (kd : Dir) (kid : IDs)
  → (((kl ≡ i → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (kid ≡ id₀ → ⊥))
      × (g kl kd kid ≡ phase-upd g i (setCell (g i) d₀ id₀ np) kl kd kid))
    ⊎ ((kl ≡ i) × (kd ≡ d₀) × (kid ≡ id₀)
       × (phase-upd g i (setCell (g i) d₀ id₀ np) kl kd kid ≡ np))
setRead⁺ g i d₀ id₀ np kl kd kid with kl ≟ i
... | no ¬p = inj₁ (inj₁ ¬p , refl)
setRead⁺ g i d₀ id₀ np kl kd kid | yes refl with kd ≟ d₀ | kid ≟ id₀
... | yes refl | yes refl = inj₂ (refl , refl , refl , refl)
... | no ¬q    | _        = inj₁ (inj₂ (inj₁ ¬q) , refl)
... | yes refl | no ¬n    = inj₁ (inj₂ (inj₂ ¬n) , refl)

-- EVERY payload is client- or server-originated, at a WRITE label
role-in : (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
        → ClientIo (input l₀ d₀ id₀) x ⊎ ServerIo (input l₀ d₀ id₀) x
role-in l₀ d₀ id₀ (t , md , ln , msg) with msgOrigin msg
... | FromInitiator = inj₁ refl
... | FromResponder = inj₂ refl

-- … and at a READ label (the roles swap: a client READS responder messages)
role-out : (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
         → ClientIo (output l₀ d₀ id₀) x ⊎ ServerIo (output l₀ d₀ id₀) x
role-out l₀ d₀ id₀ (t , md , ln , msg) with msgOrigin msg
... | FromResponder = inj₁ refl
... | FromInitiator = inj₂ refl

-- NEITHER peer moved while the cell FILLED: whichever role the payload carries,
-- that peer's ownership certificate contradicts the fired label at its own key
fill-noPeer-⊥ : (k : Link) (kd : Dir) (x : Payload)
  → ClientIo (input k kd N2N_BlockFetch) x ⊎ ServerIo (input k kd N2N_BlockFetch) x
  → NoSrvIoAt k kd N2N_BlockFetch (input k kd N2N_BlockFetch) x
  → NoCliIoAt k kd N2N_BlockFetch (input k kd N2N_BlockFetch) x → ⊥
fill-noPeer-⊥ k kd x (inj₁ ci) nsrv ncli = proj₂ ncli refl refl refl ci
fill-noPeer-⊥ k kd x (inj₂ si) nsrv ncli = proj₁ nsrv refl refl refl si

-- … and the READ mirror (the certificates' other halves)
read-noPeer-⊥ : (k : Link) (kd : Dir) (x : Payload)
  → ClientIo (output k kd N2N_BlockFetch) x ⊎ ServerIo (output k kd N2N_BlockFetch) x
  → NoSrvIoAt k kd N2N_BlockFetch (output k kd N2N_BlockFetch) x
  → NoCliIoAt k kd N2N_BlockFetch (output k kd N2N_BlockFetch) x → ⊥
read-noPeer-⊥ k kd x (inj₁ ci) nsrv ncli = proj₁ ncli refl refl refl ci
read-noPeer-⊥ k kd x (inj₂ si) nsrv ncli = proj₂ nsrv refl refl refl si

-- a fired ROW is impossible away from the peer's own key: the row carries the two key
-- equations and its label pins the CHANNEL, so each MISS reason refutes it.  The
-- channel is cased first — the row fact is label-directed, so at a variable `IDs` it
-- does not reduce at all.  Stated at an ABSTRACT key `(k , kd)`, hence shared by the
-- two hops.
srvRow-off : (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → ((k ≡ l₀ → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (N2N_BlockFetch ≡ id₀ → ⊥))
  → LIC.SrvRowP k kd bfs bfs′ (input l₀ d₀ id₀) x
  → bfs ≡ bfs′
srvRow-off k kd bfs bfs′ l₀ d₀ N2N_BlockFetch   x miss           (inj₁ (eq , _)) = eq
srvRow-off k kd bfs bfs′ l₀ d₀ N2N_BlockFetch   x (inj₁ ¬p)      (inj₂ (keq , _ , _)) = ⊥-elim (¬p (sym keq))
srvRow-off k kd bfs bfs′ l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₁ ¬q)) (inj₂ (_ , deq , _)) = ⊥-elim (¬q (sym deq))
srvRow-off k kd bfs bfs′ l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₂ ¬n)) (inj₂ _) = ⊥-elim (¬n refl)
srvRow-off k kd bfs bfs′ l₀ d₀ N2N_ChainSync    x miss (inj₁ (eq , _)) = eq
srvRow-off k kd bfs bfs′ l₀ d₀ N2N_KeepAlive    x miss (inj₁ (eq , _)) = eq
srvRow-off k kd bfs bfs′ l₀ d₀ N2N_TxSubmission x miss (inj₁ (eq , _)) = eq
srvRow-off k kd bfs bfs′ l₀ d₀ N2N_LeiosNotify  x miss (inj₁ (eq , _)) = eq
srvRow-off k kd bfs bfs′ l₀ d₀ N2N_LeiosFetch   x miss (inj₁ (eq , _)) = eq

-- … the client twin
cliRow-off : (k : Link) (kd : Dir) (bfc bfc′ : BFcPos)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → ((k ≡ l₀ → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (N2N_BlockFetch ≡ id₀ → ⊥))
  → LIC.CliRowP k kd bfc bfc′ (input l₀ d₀ id₀) x
  → bfc ≡ bfc′
cliRow-off k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x miss           (inj₁ (eq , _)) = eq
cliRow-off k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₁ ¬p)      (inj₂ (keq , _ , _)) = ⊥-elim (¬p (sym keq))
cliRow-off k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₁ ¬q)) (inj₂ (_ , deq , _)) = ⊥-elim (¬q (sym deq))
cliRow-off k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₂ ¬n)) (inj₂ _) = ⊥-elim (¬n refl)
cliRow-off k kd bfc bfc′ l₀ d₀ N2N_ChainSync    x miss (inj₁ (eq , _)) = eq
cliRow-off k kd bfc bfc′ l₀ d₀ N2N_KeepAlive    x miss (inj₁ (eq , _)) = eq
cliRow-off k kd bfc bfc′ l₀ d₀ N2N_TxSubmission x miss (inj₁ (eq , _)) = eq
cliRow-off k kd bfc bfc′ l₀ d₀ N2N_LeiosNotify  x miss (inj₁ (eq , _)) = eq
cliRow-off k kd bfc bfc′ l₀ d₀ N2N_LeiosFetch   x miss (inj₁ (eq , _)) = eq

-- the READ twins of the two row-off lemmas (the label shape differs, so the
-- label-directed fact needs its own dispatch)
srvRowR-off : (k : Link) (kd : Dir) (bfs bfs′ : BFsPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → ((k ≡ l₀ → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (N2N_BlockFetch ≡ id₀ → ⊥))
  → LIC.SrvRowP k kd bfs bfs′ (output l₀ d₀ id₀) x
  → bfs ≡ bfs′
srvRowR-off k kd bfs bfs′ l₀ d₀ N2N_BlockFetch   x miss           (inj₁ (eq , _)) = eq
srvRowR-off k kd bfs bfs′ l₀ d₀ N2N_BlockFetch   x (inj₁ ¬p)      (inj₂ (keq , _ , _)) = ⊥-elim (¬p (sym keq))
srvRowR-off k kd bfs bfs′ l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₁ ¬q)) (inj₂ (_ , deq , _)) = ⊥-elim (¬q (sym deq))
srvRowR-off k kd bfs bfs′ l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₂ ¬n)) (inj₂ _) = ⊥-elim (¬n refl)
srvRowR-off k kd bfs bfs′ l₀ d₀ N2N_ChainSync    x miss (inj₁ (eq , _)) = eq
srvRowR-off k kd bfs bfs′ l₀ d₀ N2N_KeepAlive    x miss (inj₁ (eq , _)) = eq
srvRowR-off k kd bfs bfs′ l₀ d₀ N2N_TxSubmission x miss (inj₁ (eq , _)) = eq
srvRowR-off k kd bfs bfs′ l₀ d₀ N2N_LeiosNotify  x miss (inj₁ (eq , _)) = eq
srvRowR-off k kd bfs bfs′ l₀ d₀ N2N_LeiosFetch   x miss (inj₁ (eq , _)) = eq

-- … the client twin
cliRowR-off : (k : Link) (kd : Dir) (bfc bfc′ : BFcPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → ((k ≡ l₀ → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (N2N_BlockFetch ≡ id₀ → ⊥))
  → LIC.CliRowP k kd bfc bfc′ (output l₀ d₀ id₀) x
  → bfc ≡ bfc′
cliRowR-off k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x miss           (inj₁ (eq , _)) = eq
cliRowR-off k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₁ ¬p)      (inj₂ (keq , _ , _)) = ⊥-elim (¬p (sym keq))
cliRowR-off k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₁ ¬q)) (inj₂ (_ , deq , _)) = ⊥-elim (¬q (sym deq))
cliRowR-off k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₂ ¬n)) (inj₂ _) = ⊥-elim (¬n refl)
cliRowR-off k kd bfc bfc′ l₀ d₀ N2N_ChainSync    x miss (inj₁ (eq , _)) = eq
cliRowR-off k kd bfc bfc′ l₀ d₀ N2N_KeepAlive    x miss (inj₁ (eq , _)) = eq
cliRowR-off k kd bfc bfc′ l₀ d₀ N2N_TxSubmission x miss (inj₁ (eq , _)) = eq
cliRowR-off k kd bfc bfc′ l₀ d₀ N2N_LeiosNotify  x miss (inj₁ (eq , _)) = eq
cliRowR-off k kd bfc bfc′ l₀ d₀ N2N_LeiosFetch   x miss (inj₁ (eq , _)) = eq

------------------------------------------------------------------------
-- §3  THE PER-LEG PEER FIXITY UNDER A MEDIUM-ONLY STEP.  A `break` and a medium τ
-- keep all four node records LITERAL, so all four tracked peers are fixed; the
-- accessors dispatch on the leg, so this needs the two clauses.  (`LiveLegStep`'s
-- `drain-nodes` is the same statement at `drainSucc`; this one is at an arbitrary
-- replacement medium, which is what `break-invert` hands back.)
------------------------------------------------------------------------

-- all four tracked peers are fixed when only the MEDIUM is replaced
break-peers : (l : TwoLegs) (s : SysState) (m′ : MedState)
            → (upSrv    l s ≡ upSrv    l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
            × (upClient l s ≡ upClient l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
            × (dnSrv    l s ≡ dnSrv    l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
            × (dnClient l s ≡ dnClient l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
break-peers legBD s m′ = refl , refl , refl , refl
break-peers legCD s m′ = refl , refl , refl , refl

------------------------------------------------------------------------
-- §4  *** THE HOP-PARAMETRIC ARMS. ***  ONE copy of each step class, abstracted
-- over the hop: its link, its two peers, its cell, and the propositional bridge
-- from the cell accessor to the medium key.  §5 instantiates this twice.
--
-- `LiveChanInv` is hop-generic underneath (`ChanUp`/`ChanDn` are both `ChanInv`
-- instances and `chanUp-pres`/`chanDn-pres` are both one-liners off
-- `chanInv-pres-eq`), so the arms here call `chanInv-pres-eq`/`-eq²` directly at
-- the parametric components and each instantiation's `ChanH` is the corresponding
-- banked `ChanUp`/`ChanDn` by unfolding — nothing is transported.
--
-- What this buys, measured: the api arm's TWENTY-ONE-clause label dispatch and the
-- four row-refutation tables of §2 exist ONCE for the two hops instead of twice.
------------------------------------------------------------------------

module HopArm
  (hLink : TwoLegs → Link)
  (hSrv  : TwoLegs → SysState → BFsPos)
  (hCli   : TwoLegs → SysState → BFcPos)
  (hCell : TwoLegs → SysState → CopyPhase)
  -- the hop's cell accessor IS the medium key it names, propositionally (both
  -- instances discharge this with the banked `cellUp-key`/`cellDn-key`)
  (hCell-key : (l : TwoLegs) (s : SysState)
             → hCell l s ≡ phase (med s) (hLink l) hi N2N_BlockFetch)
  where

  -- this hop's channel invariant: the banked `ChanUp`/`ChanDn` by unfolding
  ChanH : TwoLegs → SysState → Set
  ChanH l s = LCI.ChanInv (coarsenBFs (hSrv l s)) (hCell l s) (coarsenBFc (hCli l s))

  -- *** THE HOP IS FRAMED: *** both peers and the cell fixed.  This is the arm the
  -- `break`, the off-key drain and the seventeen non-BF api labels all reduce to.
  chanH-frame : (l : TwoLegs) (s s′ : SysState)
              → hSrv l s ≡ hSrv l s′
              → phase (med s′) (hLink l) hi N2N_BlockFetch
                ≡ phase (med s) (hLink l) hi N2N_BlockFetch
              → hCli l s ≡ hCli l s′
              → ChanH l s → ChanH l s′
  chanH-frame l s s′ ue ce cle iv =
    LCI.chanInv-pres-eq (cong coarsenBFs (sym ue))
      (trans (hCell-key l s′) (trans ce (sym (hCell-key l s))))
      (cong coarsenBFc (sym cle)) LCI.heFrame iv

  -- ONE medium drain preserves this hop's channel invariant.  The drained key is
  -- either this hop's own — and then the cell goes `draining x → empty` while both
  -- peers stay fixed, which is `heDrain` — or it is another key and the hop is
  -- framed.  The dichotomy is `drain-cell-at`, §2's key-keeping variant of
  -- `PipeTauMed.cell-drain-eq`.
  chanH-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                (x : Payload)
              → phase (med s) i d₀ id₀ ≡ draining x
              → hSrv l s ≡ hSrv l (drainSucc s i d₀ id₀)
              → hCli l s ≡ hCli l (drainSucc s i d₀ id₀)
              → ChanH l s → ChanH l (drainSucc s i d₀ id₀)
  chanH-drain l s i d₀ id₀ x drainEq use uce iv
    with drain-cell-at s i d₀ id₀ (hLink l) hi N2N_BlockFetch
  ... | inj₁ same = chanH-frame l s (drainSucc s i d₀ id₀) use same uce iv
  ... | inj₂ (refl , refl , refl , tgtEq) =
        LCI.chanInv-pres-eq² refl (trans (hCell-key l s) drainEq) refl
          (cong coarsenBFs (sym use))
          (trans (hCell-key l (drainSucc s i d₀ id₀)) tgtEq)
          (cong coarsenBFc (sym uce)) LCI.heDrain iv

  -- an api leaves the MEDIUM untouched, so this hop's cell is fixed
  api-frame : (l : TwoLegs) (s s′ : SysState)
            → med s ≡ med s′
            → hSrv l s ≡ hSrv l s′ → hCli l s ≡ hCli l s′
            → ChanH l s → ChanH l s′
  api-frame l s s′ medEq ue cle iv =
    chanH-frame l s s′ ue
      (cong (λ m → phase m (hLink l) hi N2N_BlockFetch) (sym medEq)) cle iv

  -- ONE visible api step preserves this hop's channel invariant.
  --
  -- The medium is untouched, so the cell is fixed and the two peers' adjacency
  -- facts decide.  All four shapes are answered, and the fourth needs no
  -- refutation: two api adjacencies COMPOSE at a fixed cell
  -- (`LiveChanInv.chan-bothApi`).
  --
  -- The dispatch is on the LABEL, and it has to be: the row facts are
  -- label-directed (a BF peer has a row only on `apiBF` and, for the server, on
  -- `done … BlockFetch`), so at a variable label they do not reduce.
  chanH-api : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
            → med s ≡ med s′
            → LAC.SrvApiRowP (hLink l) hi (hSrv l s) (hSrv l s′) e a
            → LAC.CliApiRowP (hLink l) hi (hCli l s) (hCli l s′) e a
            → ChanH l s → ChanH l s′
  -- the BF api channel: four shapes
  chanH-api l s s′ (apiBF l₀ d₀ m) v medEq (inj₁ seq) (inj₁ ceq) iv =
    api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (apiBF l₀ d₀ m) v medEq (inj₂ (refl , refl , srow)) (inj₁ ceq) iv =
    LCI.chanInv-pres-eq refl
      (trans (hCell-key l s′)
             (trans (cong (λ m₁ → phase m₁ (hLink l) hi N2N_BlockFetch) (sym medEq))
                    (sym (hCell-key l s))))
      (cong coarsenBFc (sym ceq))
      (LCI.heSrvApi (LCI.srvApiRow (hLink l) hi (coarsenBFs (hSrv l s)) m v
                      (coarsenBFs (hSrv l s′)) srow)) iv
  chanH-api l s s′ (apiBF l₀ d₀ m) v medEq (inj₁ seq) (inj₂ (refl , refl , crow)) iv =
    LCI.chanInv-pres-eq (cong coarsenBFs (sym seq))
      (trans (hCell-key l s′)
             (trans (cong (λ m₁ → phase m₁ (hLink l) hi N2N_BlockFetch) (sym medEq))
                    (sym (hCell-key l s))))
      refl
      (LCI.heCliApi (LCI.cliApiRow (hLink l) hi (coarsenBFc (hCli l s)) m v
                      (coarsenBFc (hCli l s′)) crow)) iv
  chanH-api l s s′ (apiBF l₀ d₀ m) v medEq (inj₂ (refl , refl , srow)) (inj₂ (refl , refl , crow)) iv =
    LCI.chan-frame _ _ _ _ _ _ refl
      (sym (trans (hCell-key l s′)
                  (trans (cong (λ m₁ → phase m₁ (hLink l) hi N2N_BlockFetch) (sym medEq))
                         (sym (hCell-key l s))))) refl
      (LCI.chan-bothApi (coarsenBFs (hSrv l s)) (coarsenBFs (hSrv l s′)) (hCell l s)
        (coarsenBFc (hCli l s)) (coarsenBFc (hCli l s′))
        (LCI.srvApiRow (hLink l) hi (coarsenBFs (hSrv l s)) m v
          (coarsenBFs (hSrv l s′)) srow)
        (LCI.cliApiRow (hLink l) hi (coarsenBFc (hCli l s)) m v
          (coarsenBFc (hCli l s′)) crow)
        iv)
  -- the `done` channel: only the SERVER has a row there (the twelfth `bfSnxt` row)
  chanH-api l s s′ (done l₀ d₀ N2N_BlockFetch) v medEq (inj₁ seq) ceq iv =
    api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (done l₀ d₀ N2N_BlockFetch) v medEq (inj₂ (refl , refl , srow)) ceq iv =
    LCI.chanInv-pres-eq refl
      (trans (hCell-key l s′)
             (trans (cong (λ m₁ → phase m₁ (hLink l) hi N2N_BlockFetch) (sym medEq))
                    (sym (hCell-key l s))))
      (cong coarsenBFc (sym ceq))
      (LCI.heSrvApi (LCI.srvDoneRow (hLink l) hi (coarsenBFs (hSrv l s)) v
                      (coarsenBFs (hSrv l s′)) srow)) iv
  -- every other label: a BF peer has no row at all, so both facts are fixity
  chanH-api l s s′ (done l₀ d₀ N2N_ChainSync)    v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (done l₀ d₀ N2N_KeepAlive)    v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (done l₀ d₀ N2N_TxSubmission) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (done l₀ d₀ N2N_LeiosNotify)  v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (done l₀ d₀ N2N_LeiosFetch)   v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (apiCS l₀ d₀ m)   v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (apiKA l₀ d₀ m)   v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (apiTS l₀ d₀ m)   v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (apiLN l₀ d₀ m)   v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (apiLF l₀ d₀ m)   v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (input  l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (output l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (sndmsg l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (rcvmsg l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (tx     l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (sndack l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (rcvack l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (ack    l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanH-api l s s′ (break  l₀)        v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv

  -- THE FILL ARM at this hop.
  --
  -- At the fired key the hop's cell moves, so the invariant needs a peer to have
  -- moved WITH it, and the pair (server , client) has four shapes:
  --
  --   (row , fixed) / (fixed , row) — the adjacency, one `HopEvo` arm;
  --   (row , row)     — refuted by the PAYLOAD's ROLE (`LiveChanInv`'s two
  --                     cross-peer refutations: the server's wire rows are gated on
  --                     RESPONDER tuples, the client's on INITIATOR ones, so no
  --                     payload fires both);
  --   (fixed , fixed) — refuted by the two OWNERSHIP CERTIFICATES the widened cone
  --                     hands over (grant #7).  Every payload is client- or
  --                     server-originated, and whichever role it is, THAT peer's
  --                     certificate contradicts the fired label at its own key.
  --                     This is the one case the channel invariant genuinely cannot
  --                     absorb (`cvReq` is FALSE at such a state).
  --
  -- Away from the fired key the hop is framed and a row is impossible — it carries
  -- the two key equations, which contradict the mismatch.  THE KEY COMPARISON IS
  -- THE ARM'S OWN `with`, so the medium's `phase-upd`/`setCell` term and the row's
  -- key equations reduce against the SAME scrutinees (the grant-#8 lesson).
  chanH-fill : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
               (x : Payload)
    → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                        (setCell (phase (med s) l₀) d₀ id₀ (full x)))
                     (broken (med s))
    → phase (med s) l₀ d₀ id₀ ≡ empty
    → LIC.SrvRowP (hLink l) hi (hSrv l s) (hSrv l s′) (input l₀ d₀ id₀) x
    → LIC.CliRowP (hLink l) hi (hCli l s) (hCli l s′) (input l₀ d₀ id₀) x
    → ChanH l s → ChanH l s′
  chanH-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty srow crow iv
    with setRead⁺ (phase (med s)) l₀ d₀ id₀ (full x) (hLink l) hi N2N_BlockFetch
  -- AWAY from the hop's key: the hop is framed and neither row can be inhabited
  ... | inj₁ (miss , same) =
        chanH-frame l s s′
          (srvRow-off (hLink l) hi (hSrv l s) (hSrv l s′) l₀ d₀ id₀ x miss srow)
          (trans (cong (λ m → phase m (hLink l) hi N2N_BlockFetch) sEq) (sym same))
          (cliRow-off (hLink l) hi (hCli l s) (hCli l s′) l₀ d₀ id₀ x miss crow) iv
  -- AT the hop's key: the cell filled, so exactly one of its peers moved
  ... | inj₂ (refl , refl , refl , tgt) = hit srow crow
    where
    cellSrc : hCell l s ≡ empty
    cellSrc = trans (hCell-key l s) srcEmpty
    cellTgt : hCell l s′ ≡ full x
    cellTgt = trans (hCell-key l s′)
                    (trans (cong (λ m → phase m (hLink l) hi N2N_BlockFetch) sEq) tgt)
    hit : LIC.SrvRowP (hLink l) hi (hSrv l s) (hSrv l s′)
            (input (hLink l) hi N2N_BlockFetch) x
        → LIC.CliRowP (hLink l) hi (hCli l s) (hCli l s′)
            (input (hLink l) hi N2N_BlockFetch) x
        → ChanH l s′
    -- the SERVER wrote: its row is the adjacency, the client is fixed
    hit (inj₂ (refl , refl , srowEq)) (inj₁ (ceq , _)) =
      LCI.chanInv-pres-eq² refl cellSrc refl refl cellTgt (cong coarsenBFc (sym ceq))
        (LCI.heSrvSend (LCI.srvSendRow (hLink l) hi (coarsenBFs (hSrv l s)) x
                         (coarsenBFs (hSrv l s′)) srowEq)) iv
    -- … or the CLIENT did (its request, or its `done`), and the server is fixed
    hit (inj₁ (seq , _)) (inj₂ (refl , refl , crowEq)) =
      LCI.chanInv-pres-eq² refl cellSrc refl (cong coarsenBFs (sym seq)) cellTgt refl
        (LCI.heCliSend (LCI.cliSendRow (hLink l) hi (coarsenBFc (hCli l s)) x
                         (coarsenBFc (hCli l s′)) crowEq)) iv
    -- BOTH would have written the SAME payload: impossible by its role
    hit (inj₂ (refl , refl , srowEq)) (inj₂ (refl , refl , crowEq)) =
      ⊥-elim (LCI.srvSend-cliSend-⊥
                (LCI.srvSendRow (hLink l) hi (coarsenBFs (hSrv l s)) x
                  (coarsenBFs (hSrv l s′)) srowEq)
                (LCI.cliSendRow (hLink l) hi (coarsenBFc (hCli l s)) x
                  (coarsenBFc (hCli l s′)) crowEq))
    -- NEITHER moved while the cell filled: the two ownership certificates decide it
    hit (inj₁ (seq , nsrv)) (inj₁ (ceq , ncli)) =
      ⊥-elim (fill-noPeer-⊥ (hLink l) hi x
                (role-in (hLink l) hi N2N_BlockFetch x) nsrv ncli)

  -- THE READ ARM at this hop — the fill's mirror: the cell goes
  -- `full x → draining x`, the reader is the peer whose ROLE the payload is not,
  -- and the same four shapes are answered the same four ways.
  chanH-read : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
               (x : Payload)
    → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                        (setCell (phase (med s) l₀) d₀ id₀ (draining x)))
                     (broken (med s))
    → phase (med s) l₀ d₀ id₀ ≡ full x
    → LIC.SrvRowP (hLink l) hi (hSrv l s) (hSrv l s′) (output l₀ d₀ id₀) x
    → LIC.CliRowP (hLink l) hi (hCli l s) (hCli l s′) (output l₀ d₀ id₀) x
    → ChanH l s → ChanH l s′
  chanH-read l s s′ l₀ d₀ id₀ x sEq srcFull srow crow iv
    with setRead⁺ (phase (med s)) l₀ d₀ id₀ (draining x) (hLink l) hi N2N_BlockFetch
  ... | inj₁ (miss , same) =
        chanH-frame l s s′
          (srvRowR-off (hLink l) hi (hSrv l s) (hSrv l s′) l₀ d₀ id₀ x miss srow)
          (trans (cong (λ m → phase m (hLink l) hi N2N_BlockFetch) sEq) (sym same))
          (cliRowR-off (hLink l) hi (hCli l s) (hCli l s′) l₀ d₀ id₀ x miss crow) iv
  ... | inj₂ (refl , refl , refl , tgt) = hit srow crow
    where
    cellSrc : hCell l s ≡ full x
    cellSrc = trans (hCell-key l s) srcFull
    cellTgt : hCell l s′ ≡ draining x
    cellTgt = trans (hCell-key l s′)
                    (trans (cong (λ m → phase m (hLink l) hi N2N_BlockFetch) sEq) tgt)
    hit : LIC.SrvRowP (hLink l) hi (hSrv l s) (hSrv l s′)
            (output (hLink l) hi N2N_BlockFetch) x
        → LIC.CliRowP (hLink l) hi (hCli l s) (hCli l s′)
            (output (hLink l) hi N2N_BlockFetch) x
        → ChanH l s′
    -- the SERVER read (the client's request or its `done` leaves the cell)
    hit (inj₂ (refl , refl , srowEq)) (inj₁ (ceq , _)) =
      LCI.chanInv-pres-eq² refl cellSrc refl refl cellTgt (cong coarsenBFc (sym ceq))
        (LCI.heSrvRead (LCI.srvReadRow (hLink l) hi (coarsenBFs (hSrv l s)) x
                         (coarsenBFs (hSrv l s′)) srowEq)) iv
    -- … or the CLIENT did — the DELIVERY, the step the whole campaign is about
    hit (inj₁ (seq , _)) (inj₂ (refl , refl , crowEq)) =
      LCI.chanInv-pres-eq² refl cellSrc refl (cong coarsenBFs (sym seq)) cellTgt refl
        (LCI.heCliRead (LCI.cliReadRow (hLink l) hi (coarsenBFc (hCli l s)) x
                         (coarsenBFc (hCli l s′)) crowEq)) iv
    -- BOTH would have read the same payload: impossible by its role
    hit (inj₂ (refl , refl , srowEq)) (inj₂ (refl , refl , crowEq)) =
      ⊥-elim (LCI.srvRead-cliRead-⊥
                (LCI.srvReadRow (hLink l) hi (coarsenBFs (hSrv l s)) x
                  (coarsenBFs (hSrv l s′)) srowEq)
                (LCI.cliReadRow (hLink l) hi (coarsenBFc (hCli l s)) x
                  (coarsenBFc (hCli l s′)) crowEq))
    -- NEITHER moved while the cell drained into a reader: the certificates decide
    hit (inj₁ (seq , nsrv)) (inj₁ (ceq , ncli)) =
      ⊥-elim (read-noPeer-⊥ (hLink l) hi x
                (role-out (hLink l) hi N2N_BlockFetch x) nsrv ncli)

------------------------------------------------------------------------
-- §5  THE TWO INSTANCES, AND THE LEG'S TWO HOPS PER STEP CLASS.
------------------------------------------------------------------------

-- the leg's UP hop: node A's BF server, the up cell, the relay's BF client
module HUp = HopArm upLink upSrv upClient cellUp cellUp-key

-- … and its DOWN hop: the relay's BF server, the down cell, node D's BF client
module HDn = HopArm dnLink dnSrv dnClient cellDn cellDn-key

-- ONE `break` preserves BOTH hops: a break moves the medium's BROKEN bits only, so
-- the phase function is preserved (`break-invert`'s third component) and all four
-- node records are LITERAL in the successor
chanLeg-break : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
                (step : radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M)
              → LCI.ChanLeg l (toSys r)
              → LCI.ChanLeg l (toSys (proj₁ (LA.evStepJ-break l r l₀ step)))
chanLeg-break l r l₀ {a} step (ivU , ivD) =
  let (m′ , medStep , pheq , Meq , _) = break-invert r l₀ {a} step
      s′ : SysState
      s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
      (useU , uceU , useD , uceD) = break-peers l (toSys r) m′
  in  HUp.chanH-frame l (toSys r) s′ useU
        (cong (λ g → g (upLink l) hi N2N_BlockFetch) pheq) uceU ivU
    , HDn.chanH-frame l (toSys r) s′ useD
        (cong (λ g → g (dnLink l) hi N2N_BlockFetch) pheq) uceD ivD

-- ONE medium drain preserves BOTH hops (`LiveLegStep.drain-nodes` reports all four
-- peers' fixity, and the drained key hits at most one of the two cells)
chanLeg-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                (x : Payload)
              → phase (med s) i d₀ id₀ ≡ draining x
              → LCI.ChanLeg l s → LCI.ChanLeg l (drainSucc s i d₀ id₀)
chanLeg-drain l s i d₀ id₀ x drainEq (ivU , ivD) =
  let (_ , _ , _ , _ , use , dse , uce , dce) = LS.drain-nodes l s i d₀ id₀
  in  HUp.chanH-drain l s i d₀ id₀ x drainEq use uce ivU
    , HDn.chanH-drain l s i d₀ id₀ x drainEq dse dce ivD

-- ONE visible api step preserves BOTH hops, off the api cone's two per-leg row
-- pairs (the UP pair from grant #8's threading, the DOWN pair from
-- `LiveLegApiExpose` §8's node-D re-mirror)
chanLeg-api : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
            → med s ≡ med s′
            → LAC.SrvApiRowP (upLink l) hi (upSrv l s) (upSrv l s′) e a
              × LAC.CliApiRowP (upLink l) hi (upClient l s) (upClient l s′) e a
            → LAC.SrvApiRowP (dnLink l) hi (dnSrv l s) (dnSrv l s′) e a
              × LAC.CliApiRowP (dnLink l) hi (dnClient l s) (dnClient l s′) e a
            → LCI.ChanLeg l s → LCI.ChanLeg l s′
chanLeg-api l s s′ e a medEq (srowU , crowU) (srowD , crowD) (ivU , ivD) =
    HUp.chanH-api l s s′ e a medEq srowU crowU ivU
  , HDn.chanH-api l s s′ e a medEq srowD crowD ivD

------------------------------------------------------------------------
-- §5b  THE io CONE'S FOUR ROW SLOTS, per leg and per hop.  `AllSrvP`/`AllCliP` are
-- the four tracked peers in the order (up BD, up CD, dn BD, dn CD), so the down
-- hop's rows were ALREADY reported — grant #7 stated them for all four peers at
-- once, and only the two selectors below were missing.
------------------------------------------------------------------------

upSrvRow : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
         → LIC.AllSrvP s s′ e a
         → LIC.SrvRowP (upLink l) hi (upSrv l s) (upSrv l s′) e a
upSrvRow legBD s s′ e a (q1 , _ , _ , _) = proj₂ (proj₂ (proj₂ q1))
upSrvRow legCD s s′ e a (_ , q2 , _ , _) = proj₂ (proj₂ (proj₂ q2))

upCliRow : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
         → LIC.AllCliP s s′ e a
         → LIC.CliRowP (upLink l) hi (upClient l s) (upClient l s′) e a
upCliRow legBD s s′ e a (c1 , _ , _ , _) = proj₂ (proj₂ c1)
upCliRow legCD s s′ e a (_ , c2 , _ , _) = proj₂ (proj₂ c2)

dnSrvRow : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
         → LIC.AllSrvP s s′ e a
         → LIC.SrvRowP (dnLink l) hi (dnSrv l s) (dnSrv l s′) e a
dnSrvRow legBD s s′ e a (_ , _ , q3 , _) = proj₂ (proj₂ (proj₂ q3))
dnSrvRow legCD s s′ e a (_ , _ , _ , q4) = proj₂ (proj₂ (proj₂ q4))

dnCliRow : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
         → LIC.AllCliP s s′ e a
         → LIC.CliRowP (dnLink l) hi (dnClient l s) (dnClient l s′) e a
dnCliRow legBD s s′ e a (_ , _ , c3 , _) = proj₂ (proj₂ c3)
dnCliRow legCD s s′ e a (_ , _ , _ , c4) = proj₂ (proj₂ c4)

-- (T5, grant #11) … and the FIFTH slot, the leg's down-hop CS SERVER.  The new cone
-- view reports the two tracked CS servers in leg order, so this is the whole of the
-- per-leg selection — and the leg being a CONSTRUCTOR is what makes the cone's
-- node-field form and the coupling's `dnCSs` form convertible
dnCssRow : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
         → LIC.AllCssP s s′ e a
         → LIC.CssRowP (dnLink l) hi (dnCSs l s) (dnCSs l s′) e a
-- (T6c, grant #12) … and `proj₁` because the cone's CS-server slot is now the PAIR
-- `LiveLegIoCone.CssPairP` — grant #11's frozen fact (this one) beside grant #12's
-- label-directed twin.  `LiveDrvBF`'s four io arms keep their premise TYPE exactly.
dnCssRow legBD s s′ e a (q1 , _) = proj₁ q1
dnCssRow legCD s s′ e a (_ , q2) = proj₁ q2

-- (T7, grant #12) … and the SIXTH, the leg's UP-hop CS CLIENT.  The granted cone reports
-- the four CS clients up-then-down in leg order (`LIC.AllCscP`), so the two UP ones are
-- its first and third components — the same selection `csIoUp` makes, and stated at
-- `upCSc` rather than at `LCC.upCScOf` because that is the form `LiveDrvBF`'s io arms
-- take.  The two names denote the SAME node fields, and the leg dispatch is what makes
-- them convertible (`dnCSs`/`dnCSsOf` needed an explicit bridge only because THAT pair
-- meets at a variable leg — see `LiveRelayCS.dnCSs-is-of`)
upCscRow : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
         → LIC.AllCscP s s′ e a
         → LIC.CscIoRowP (upLink l) hi (upCSc l s) (upCSc l s′) e a
upCscRow legBD s s′ e a csc = proj₁ csc
upCscRow legCD s s′ e a csc = proj₁ (proj₂ csc)

-- ONE io FILL preserves BOTH hops
chanLeg-fill : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
               (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (full x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ empty
  → LIC.AllSrvP s s′ (input l₀ d₀ id₀) x
  → LIC.AllCliP s s′ (input l₀ d₀ id₀) x
  → LCI.ChanLeg l s → LCI.ChanLeg l s′
chanLeg-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty srvP cliP (ivU , ivD) =
    HUp.chanH-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty
      (upSrvRow l s s′ (input l₀ d₀ id₀) x srvP)
      (upCliRow l s s′ (input l₀ d₀ id₀) x cliP) ivU
  , HDn.chanH-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty
      (dnSrvRow l s s′ (input l₀ d₀ id₀) x srvP)
      (dnCliRow l s s′ (input l₀ d₀ id₀) x cliP) ivD

-- … and ONE io READ
chanLeg-read : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
               (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (draining x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ full x
  → LIC.AllSrvP s s′ (output l₀ d₀ id₀) x
  → LIC.AllCliP s s′ (output l₀ d₀ id₀) x
  → LCI.ChanLeg l s → LCI.ChanLeg l s′
chanLeg-read l s s′ l₀ d₀ id₀ x sEq srcFull srvP cliP (ivU , ivD) =
    HUp.chanH-read l s s′ l₀ d₀ id₀ x sEq srcFull
      (upSrvRow l s s′ (output l₀ d₀ id₀) x srvP)
      (upCliRow l s s′ (output l₀ d₀ id₀) x cliP) ivU
  , HDn.chanH-read l s s′ l₀ d₀ id₀ x sEq srcFull
      (dnSrvRow l s s′ (output l₀ d₀ id₀) x srvP)
      (dnCliRow l s s′ (output l₀ d₀ id₀) x cliP) ivD

------------------------------------------------------------------------
-- §5c  (T1) THE DRIVER-TAIL COUPLING'S TWO FRAME HALVES.  The medium-τ and
-- `break` classes fix BOTH of S1's components, so each is one call to
-- `LiveDrvBF.drvBF-fixed` at the same arguments the channel half's own arm takes —
-- the api and io halves need the cones' slots and are inlined at §6's arms.
------------------------------------------------------------------------

-- the relay driver's phase and the leg's down server across a `break`: the medium's
-- BROKEN bits move and all four node records are LITERAL, so both are `refl` once
-- the leg is a constructor (`break-peers`' shape, at the two slots S1 reads)
break-drv : (l : TwoLegs) (s : SysState) (m′ : MedState)
          → (relayOf l s ≡ relayOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
            × (dnSrv   l s ≡ dnSrv   l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
break-drv legBD s m′ = refl , refl
break-drv legCD s m′ = refl , refl

-- ONE medium drain preserves the coupling: `drain-nodes` reports the relay phase
-- (its second component) and the leg's down server (its sixth) as fixed
drvBF-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
            → LDB.DrvBF l s → LDB.DrvBF l (drainSucc s i d₀ id₀)
drvBF-drain l s i d₀ id₀ db =
  let (_ , re , _ , _ , _ , dse , _ , _) = LS.drain-nodes l s i d₀ id₀
  -- (T5) the drain keeps all four node records LITERAL (`PipeTauMed.drainSucc:87-91`),
  -- so the coupling's third component rides on `refl`
  in  LDB.drvBF-fixed l s (drainSucc s i d₀ id₀) re dse
        (LDB.dnCSs-fix l s (drainSucc s i d₀ id₀) refl refl)
        -- (T7) the same two `refl`s serve the UP-hop CLIENT: the drain keeps all four
        -- node records LITERAL, so the coupling's fourth component rides too
        (LDB.upCSc-fix l s (drainSucc s i d₀ id₀) refl refl) db

-- … and ONE `break` does too
drvBF-break : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
              (step : radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M)
            → LDB.DrvBF l (toSys r)
            → LDB.DrvBF l (toSys (proj₁ (LA.evStepJ-break l r l₀ step)))
drvBF-break l r l₀ {a} step db =
  let (m′ , _ , _ , _ , _) = break-invert r l₀ {a} step
      s′ : SysState
      s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
      (pe , se) = break-drv l (toSys r) m′
  in  LDB.drvBF-fixed l (toSys r) s′ pe se
        (LDB.dnCSs-fix l (toSys r) s′ refl refl)
        -- (T7) … and at a `break` too: the medium's BROKEN bits move and all four node
        -- records are LITERAL
        (LDB.upCSc-fix l (toSys r) s′ refl refl) db

------------------------------------------------------------------------
-- §5c⁺  (T11g) *** THE FIFTH FACTOR's THIRD HALF — `LiveDrvBFD.BFFresh`, FOLDED INTO
-- `DrvBF` RATHER THAN TRAILING BEHIND IT. ***  It walks the SAME down-BlockFetch hop,
-- so every one of `DrvBF`'s five arm sites already holds what its classes want.
--
-- *** THE fill/read ARMS ARE A FAITHFUL TRANSCRIPTION OF `HopArm.chanH-fill`/`-read`
-- AT THE SAME HOP *** — the same `setRead⁺` key dichotomy, the same four peer shapes in
-- the same order, and the same two refutations closing the last two.  Only the object
-- the four shapes BUILD differs.  KEEP IN SYNC with `HDn`'s pair.
--
-- *** THESE FOUR ARE PARKED UNTIL THE api ARM LANDS. ***  The factor swap needs all
-- five arms at once (`mkU` takes one argument per factor), and the api arm is waiting
-- on the dn BF server's fixity at the five in-region advances (`LiveDrvBFD` §3b).  They
-- are landed now, alone and green, because they were the certain half — and because a
-- certain re-creation is still a PAID one, so paying it once and banking it is worth
-- more than carrying it as a plan.
------------------------------------------------------------------------

-- the leg's four BF-hop slots across a drain / a `break`, `dnSlots-*`'s shape (both
-- keep all four node records LITERAL, so each is a per-leg `refl`)
bfSlots-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
  → (relayOf l s ≡ relayOf l (drainSucc s i d₀ id₀))
    × (dnSrv l s ≡ dnSrv l (drainSucc s i d₀ id₀))
    × (dnClient l s ≡ dnClient l (drainSucc s i d₀ id₀))
    × (phOf l s ≡ phOf l (drainSucc s i d₀ id₀))
bfSlots-drain legBD s i d₀ id₀ = refl , refl , refl , refl
bfSlots-drain legCD s i d₀ id₀ = refl , refl , refl , refl

bfSlots-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
  → (relayOf l s ≡ relayOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
    × (dnSrv l s ≡ dnSrv l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
    × (dnClient l s ≡ dnClient l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
    × (phOf l s ≡ phOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
bfSlots-break legBD s m′ = refl , refl , refl , refl
bfSlots-break legCD s m′ = refl , refl , refl , refl

-- ONE medium drain: the drained key is this hop's own — and then the cell goes
-- `draining x → empty` with every position fixed, which is §2's own `bfFresh-drainS` —
-- or it is another key and the hop is framed.  `chanH-drain`'s dichotomy verbatim
bfFreshU-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                 (x : Payload)
               → phase (med s) i d₀ id₀ ≡ draining x
               → LBFD.BFFresh l s → LBFD.BFFresh l (drainSucc s i d₀ id₀)
bfFreshU-drain l s i d₀ id₀ x drainEq = arms (bfSlots-drain l s i d₀ id₀)
  where
  arms : (relayOf l s ≡ relayOf l (drainSucc s i d₀ id₀))
         × (dnSrv l s ≡ dnSrv l (drainSucc s i d₀ id₀))
         × (dnClient l s ≡ dnClient l (drainSucc s i d₀ id₀))
         × (phOf l s ≡ phOf l (drainSucc s i d₀ id₀))
       → LBFD.BFFresh l s → LBFD.BFFresh l (drainSucc s i d₀ id₀)
  arms (peq , seq , keq , deq) = keyArms (drain-cell-at s i d₀ id₀ (dnLink l) hi N2N_BlockFetch)
    where
    keyArms : _ → LBFD.BFFresh l s → LBFD.BFFresh l (drainSucc s i d₀ id₀)
    keyArms (inj₁ same) =
      LBFD.bfFresh-frame l s _ peq seq
        (trans (cellDn-key l s) (trans (sym same) (sym (cellDn-key l _)))) keq deq
    keyArms (inj₂ (refl , refl , refl , tgtEq)) =
      LBFD.bfFresh-drainS l s _ x peq (trans (cellDn-key l s) drainEq)
        (trans (cellDn-key l _) tgtEq) seq keq deq

-- … and ONE `break`: only the medium's BROKEN bits move, so the hop is framed and the
-- cell rides one `cong`
bfFreshU-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
               → phase m′ ≡ phase (med s)
               → LBFD.BFFresh l s
               → LBFD.BFFresh l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
bfFreshU-break l s m′ pheq = arms (bfSlots-break l s m′)
  where
  arms : (relayOf l s ≡ relayOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
         × (dnSrv l s ≡ dnSrv l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
         × (dnClient l s ≡ dnClient l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
         × (phOf l s ≡ phOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
       → LBFD.BFFresh l s → LBFD.BFFresh l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
  arms (peq , seq , keq , deq) =
    LBFD.bfFresh-frame l s _ peq seq
      (trans (cellDn-key l s)
        (trans (sym (cong (λ g → g (dnLink l) hi N2N_BlockFetch) pheq))
               (sym (cellDn-key l _)))) keq deq

-- *** THE io FILL — `HopArm.chanH-fill`'s four shapes, building `BFFresh`. ***  The
-- SERVER's four wire-sends all start OUTSIDE `SrvFreshBF`, so §2 refutes them by the
-- server conjunct alone; the CLIENT's REQUEST row is the one step that ESTABLISHES the
-- freshness correlation and its `done` row starts outside the client region; both
-- writing the same payload is impossible by ROLE; and neither writing while the cell
-- fills is closed by the two ownership certificates
bfFreshU-fill : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
                (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (full x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ empty
  → relayOf l s ≡ relayOf l s′
  → phOf l s ≡ phOf l s′
  → LIC.SrvRowP (dnLink l) hi (dnSrv l s) (dnSrv l s′) (input l₀ d₀ id₀) x
  → LIC.CliRowP (dnLink l) hi (dnClient l s) (dnClient l s′) (input l₀ d₀ id₀) x
  → LBFD.BFFresh l s → LBFD.BFFresh l s′
bfFreshU-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty peq deq srow crow
  with setRead⁺ (phase (med s)) l₀ d₀ id₀ (full x) (dnLink l) hi N2N_BlockFetch
... | inj₁ (miss , same) =
      LBFD.bfFresh-frame l s s′ peq
        (srvRow-off (dnLink l) hi (dnSrv l s) (dnSrv l s′) l₀ d₀ id₀ x miss srow)
        (trans (cellDn-key l s)
          (trans (sym (trans (cong (λ m → phase m (dnLink l) hi N2N_BlockFetch) sEq)
                             (sym same)))
                 (sym (cellDn-key l s′))))
        (cliRow-off (dnLink l) hi (dnClient l s) (dnClient l s′) l₀ d₀ id₀ x miss crow)
        deq
... | inj₂ (refl , refl , refl , tgt) = hit srow crow
  where
  cellSrc : cellDn l s ≡ empty
  cellSrc = trans (cellDn-key l s) srcEmpty
  cellTgt : cellDn l s′ ≡ full x
  cellTgt = trans (cellDn-key l s′)
                  (trans (cong (λ m → phase m (dnLink l) hi N2N_BlockFetch) sEq) tgt)
  hit : LIC.SrvRowP (dnLink l) hi (dnSrv l s) (dnSrv l s′)
          (input (dnLink l) hi N2N_BlockFetch) x
      → LIC.CliRowP (dnLink l) hi (dnClient l s) (dnClient l s′)
          (input (dnLink l) hi N2N_BlockFetch) x
      → LBFD.BFFresh l s → LBFD.BFFresh l s′
  hit (inj₂ (refl , refl , srowEq)) (inj₁ (ceq , _)) =
    LBFD.bfFresh-srvSendS l s s′ x peq cellSrc cellTgt ceq deq
      (LCI.srvSendRow (dnLink l) hi (coarsenBFs (dnSrv l s)) x
        (coarsenBFs (dnSrv l s′)) srowEq)
  hit (inj₁ (seq , _)) (inj₂ (refl , refl , crowEq)) =
    LBFD.bfFresh-cliSendS l s s′ x peq cellSrc cellTgt seq deq
      (LCI.cliSendRow (dnLink l) hi (coarsenBFc (dnClient l s)) x
        (coarsenBFc (dnClient l s′)) crowEq)
  hit (inj₂ (refl , refl , srowEq)) (inj₂ (refl , refl , crowEq)) =
    ⊥-elim (LCI.srvSend-cliSend-⊥
              (LCI.srvSendRow (dnLink l) hi (coarsenBFs (dnSrv l s)) x
                (coarsenBFs (dnSrv l s′)) srowEq)
              (LCI.cliSendRow (dnLink l) hi (coarsenBFc (dnClient l s)) x
                (coarsenBFc (dnClient l s′)) crowEq))
  hit (inj₁ (seq , nsrv)) (inj₁ (ceq , ncli)) =
    ⊥-elim (fill-noPeer-⊥ (dnLink l) hi x
              (role-in (dnLink l) hi N2N_BlockFetch x) nsrv ncli)

-- … and the io READ, the fill's mirror: the SERVER's request read lands INSIDE the
-- region (the step §2's own arm names) and its `done` read is refuted by the cell pin;
-- all four CLIENT reads are refuted, two by the pin and two by the client region
bfFreshU-read : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
                (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (draining x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ full x
  → relayOf l s ≡ relayOf l s′
  → phOf l s ≡ phOf l s′
  → LIC.SrvRowP (dnLink l) hi (dnSrv l s) (dnSrv l s′) (output l₀ d₀ id₀) x
  → LIC.CliRowP (dnLink l) hi (dnClient l s) (dnClient l s′) (output l₀ d₀ id₀) x
  → LBFD.BFFresh l s → LBFD.BFFresh l s′
bfFreshU-read l s s′ l₀ d₀ id₀ x sEq srcFull peq deq srow crow
  with setRead⁺ (phase (med s)) l₀ d₀ id₀ (draining x) (dnLink l) hi N2N_BlockFetch
... | inj₁ (miss , same) =
      LBFD.bfFresh-frame l s s′ peq
        (srvRowR-off (dnLink l) hi (dnSrv l s) (dnSrv l s′) l₀ d₀ id₀ x miss srow)
        (trans (cellDn-key l s)
          (trans (sym (trans (cong (λ m → phase m (dnLink l) hi N2N_BlockFetch) sEq)
                             (sym same)))
                 (sym (cellDn-key l s′))))
        (cliRowR-off (dnLink l) hi (dnClient l s) (dnClient l s′) l₀ d₀ id₀ x miss crow)
        deq
... | inj₂ (refl , refl , refl , tgt) = hit srow crow
  where
  cellSrc : cellDn l s ≡ full x
  cellSrc = trans (cellDn-key l s) srcFull
  cellTgt : cellDn l s′ ≡ draining x
  cellTgt = trans (cellDn-key l s′)
                  (trans (cong (λ m → phase m (dnLink l) hi N2N_BlockFetch) sEq) tgt)
  hit : LIC.SrvRowP (dnLink l) hi (dnSrv l s) (dnSrv l s′)
          (output (dnLink l) hi N2N_BlockFetch) x
      → LIC.CliRowP (dnLink l) hi (dnClient l s) (dnClient l s′)
          (output (dnLink l) hi N2N_BlockFetch) x
      → LBFD.BFFresh l s → LBFD.BFFresh l s′
  hit (inj₂ (refl , refl , srowEq)) (inj₁ (ceq , _)) =
    LBFD.bfFresh-srvReadS l s s′ x peq cellSrc cellTgt ceq deq
      (LCI.srvReadRow (dnLink l) hi (coarsenBFs (dnSrv l s)) x
        (coarsenBFs (dnSrv l s′)) srowEq)
  hit (inj₁ (seq , _)) (inj₂ (refl , refl , crowEq)) =
    LBFD.bfFresh-cliReadS l s s′ x peq cellSrc cellTgt seq deq
      (LCI.cliReadRow (dnLink l) hi (coarsenBFc (dnClient l s)) x
        (coarsenBFc (dnClient l s′)) crowEq)
  hit (inj₂ (refl , refl , srowEq)) (inj₂ (refl , refl , crowEq)) =
    ⊥-elim (LCI.srvRead-cliRead-⊥
              (LCI.srvReadRow (dnLink l) hi (coarsenBFs (dnSrv l s)) x
                (coarsenBFs (dnSrv l s′)) srowEq)
              (LCI.cliReadRow (dnLink l) hi (coarsenBFc (dnClient l s)) x
                (coarsenBFc (dnClient l s′)) crowEq))
  hit (inj₁ (seq , nsrv)) (inj₁ (ceq , ncli)) =
    ⊥-elim (read-noPeer-⊥ (dnLink l) hi x
              (role-out (dnLink l) hi N2N_BlockFetch x) nsrv ncli)

-- *** (T11h) THE api ARM — the fifth and LAST of the fold, and the ONE place the
-- which-node-fired question is asked on this axis. ***  `dnJointU-api`'s four-way
-- dispatch at the BlockFetch peers, and it is FOUR-way for the same reason: the guard
-- sits on the RELAY's phase, so the relay's own advance decides first and node D's move
-- decides second.
--
-- The two facts that made it wait (`LiveDrvBFD` §3b) both arrive as CONE components:
-- `DnSrvDrv`'s new third member (`LAC.DnSrvPre`) carries the dn BF SERVER's fixity
-- across the relay's three IN-REGION produce hops, and the node-D field's fixity arm
-- carries the dn BF CLIENT's.  Neither is derivable at this consumer — both are
-- label-correlated, and the correlation exists only where the label is a literal.
------------------------------------------------------------------------

-- the two things the freshness clause reads off the cone's node-D field: node D held
-- BOTH its phase and its dn BF client, or it fired and §2c's producer gives the hop
BfNodeD : (l : TwoLegs) (s s′ : SysState) → Set
BfNodeD l s s′ =
    ((phOf l s ≡ phOf l s′) × (dnClient l s ≡ dnClient l s′))
  ⊎ LBFD.BFCliDrvAdj (coarsenBFc (dnClient l s)) (phOf l s)
                     (coarsenBFc (dnClient l s′)) (phOf l s′)

-- … and the narrowing that produces it.  `dnJointU-api`'s `narrow` at the OTHER axis:
-- an explicit dispatch and not a `with`, for the banked reason
--
-- (F107  *** THE NODE-D FIELD's THIRD FIXITY COMPONENT IS LOAD-BEARING, and it is why
-- the field had to be WIDENED at all. ***)  read the fixity arm's SECOND component (the
-- dn CS CLIENT's, which was already there) as the BF client's — arity-preserving, the
-- clause set untouched, and it is exactly the shape a reader who thinks "node D held its
-- client" is one fact rather than two would write.  *** RED ***:
-- `LiveChanJoin.agda:1276.61-64: [UnequalTerms] …SysNode.CScPos blkA != BFcPos of type
-- Set … when checking that the expression keq has type dnClient l s ≡ dnClient l s′`,
-- EXIT=42.  The two peers sit at the SAME KEY `(dnLink l , hi)` and are different
-- POSITION types, which is the whole reason `deRowsBD`'s `CliApiRowP` cannot stand in
-- for the equation either (§8 (i-b)'s trap at node D's own peer).  Reverted by string
-- inversion, `git status` clean after.
bfNodeD-of : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
             {e : Net_Api Payload X} {a : X}
           → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′)
               × (dnClient l s ≡ dnClient l s′))
              ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                    ─[ ev (evl (evLabel X e a)) ]─►
                    decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                 × ConsAdv (phOf l s) (phOf l s′)
                 × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                     (LCC.dnCScOf l s′) e a
                 × LAC.CliReqLand (dnLink l) hi (dnClient l s) (dnClient l s′) e a
                 × (phOf l s ≡ cp3
                    → Σ[ b″ ∈ Block₃ ]
                        (coarsenBFc (dnClient l s) ≡ NS.bcAblk b″))))
           → LAC.CliApiRowP (dnLink l) hi (dnClient l s) (dnClient l s′) e a
           → BfNodeD l s s′
bfNodeD-of l s s′ (inj₁ (deq , _ , keq)) crow = inj₁ (deq , keq)
bfNodeD-of l s s′ (inj₂ (drvD , cadv , _ , reqLand , anch)) crow =
  inj₂ (LBFD.bfCliDrvAdj-of (dnLink l) (cblkOf l s) (phOf l s) (phOf l s′)
          (dnClient l s) (dnClient l s′) drvD cadv crow reqLand anch)

bfFreshU-api : (l : TwoLegs) (s s′ : SysState)
             → med s ≡ med s′
             → LAC.DnSrvDrv l s s′
             → ((relayOf l s ≡ relayOf l s′)
                ⊎ LAC.RelayAdv (relayOf l s) (relayOf l s′))
             → BfNodeD l s s′
             → LBFD.BFFresh l s → LBFD.BFFresh l s′
bfFreshU-api l s s′ medEq dnDrv relayAdv nd = arms dnDrv relayAdv nd
  where
  -- an api leaves the MEDIUM alone, so this hop's cell rides one `cong`
  cellEq : cellDn l s ≡ cellDn l s′
  cellEq = trans (cellDn-key l s)
             (trans (cong (λ m → phase m (dnLink l) hi N2N_BlockFetch) medEq)
                    (sym (cellDn-key l s′)))
  -- the relay's phase AND the dn server both held: frame, or node D's own api class
  fixed : relayOf l s ≡ relayOf l s′ → dnSrv l s ≡ dnSrv l s′
        → BfNodeD l s s′ → LBFD.BFFresh l s → LBFD.BFFresh l s′
  fixed peq seq (inj₁ (deq , keq)) = LBFD.bfFresh-frame l s s′ peq seq cellEq keq deq
  fixed peq seq (inj₂ adj)         = LBFD.bfFresh-nodeDApi l s s′ peq seq cellEq adj
  -- the relay ADVANCED with the dn server held: §0(3)'s backward-closure dispatch
  -- decides — the source is in the region (so the guard transports) or the successor is
  -- outside it (so the whole obligation is vacuous)
  moved : LAC.RelayAdv (relayOf l s) (relayOf l s′) → dnSrv l s ≡ dnSrv l s′
        → BfNodeD l s s′ → LBFD.BFFresh l s → LBFD.BFFresh l s′
  moved ra seq nd′ = guarded (LBFD.relayAdvBF-guard _ _ ra) nd′
    where
    guarded : LBFD.RelayFreshBF (relayOf l s)
              ⊎ (LBFD.RelayFreshBF (relayOf l s′) → ⊥)
            → BfNodeD l s s′ → LBFD.BFFresh l s → LBFD.BFFresh l s′
    guarded (inj₂ nof) _                 = LBFD.bfFresh-relayOut l s s′ nof
    guarded (inj₁ g) (inj₁ (deq , keq))  = LBFD.bfFresh-relayIn l s s′ g seq cellEq keq deq
    guarded (inj₁ g) (inj₂ adj)          = LBFD.bfFresh-relayInApi l s s′ g seq cellEq adj
  -- the cone's own dispatch, on EXPLICIT arguments (the banked `arms` idiom)
  arms : LAC.DnSrvDrv l s s′
       → ((relayOf l s ≡ relayOf l s′)
          ⊎ LAC.RelayAdv (relayOf l s) (relayOf l s′))
       → BfNodeD l s s′ → LBFD.BFFresh l s → LBFD.BFFresh l s′
  arms (inj₁ (peq , seq)) _ nd′ = fixed peq seq nd′
  -- the relay LANDED past its own `reqBFRange` emit: `PastAreq` against the region
  arms (inj₂ (_ , _ , inj₂ (bb , qq , peq′ , past))) _ _ =
    LBFD.bfFresh-relayOut l s s′
      (λ g → LBFD.pastAreq-⊮ bb qq past (subst LBFD.RelayFreshBF peq′ g))
  arms (inj₂ (_ , _ , inj₁ seq)) (inj₁ peq) nd′ = fixed peq seq nd′
  arms (inj₂ (_ , _ , inj₁ seq)) (inj₂ ra)  nd′ = moved ra seq nd′

-- *** (B, cellCp3) THE FIFTH FACTOR's THIRD MEMBER AT THE STATE LEVEL. ***  `DnIdl`
-- reads node D's phase and its down BF client and NOTHING else — no cell, no server,
-- no relay phase — so four of its five classes are the SAME frame off the two slot
-- tuples above, and the api class is one application of the `BfNodeD` the freshness
-- half already reads (bound at the site, per M-5).  No `dnIdlU-api` exists for that
-- reason: `LBFD.dnIdl-api` IS the arm.
dnIdlU-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
             → LBFD.DnIdl l s → LBFD.DnIdl l (drainSucc s i d₀ id₀)
dnIdlU-drain l s i d₀ id₀ =
  LBFD.dnIdl-frame l s _ (proj₂ (proj₂ (proj₂ (bfSlots-drain l s i d₀ id₀))))
    (cong coarsenBFc (proj₁ (proj₂ (proj₂ (bfSlots-drain l s i d₀ id₀)))))

dnIdlU-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
             → LBFD.DnIdl l s → LBFD.DnIdl l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
dnIdlU-break l s m′ =
  LBFD.dnIdl-frame l s _ (proj₂ (proj₂ (proj₂ (bfSlots-break l s m′))))
    (cong coarsenBFc (proj₁ (proj₂ (proj₂ (bfSlots-break l s m′)))))

-- the two io classes: node D's phase off the io cone's own driver fixity, and its
-- client off `LiveDrvBF` §3's two new CLIENT selectors — the key dispatch the cell
-- needs is not needed here, because `CliRowP`'s own two arms are the answer
dnIdlU-fill : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
              (x : Payload)
            → phOf l s ≡ phOf l s′
            → LIC.CliRowP (dnLink l) hi (dnClient l s) (dnClient l s′)
                (input l₀ d₀ id₀) x
            → LBFD.DnIdl l s → LBFD.DnIdl l s′
dnIdlU-fill l s s′ l₀ d₀ id₀ x deq crow =
  LBFD.dnIdl-fill l s s′ x deq
    (LDB.cliFill-adj (dnLink l) hi (dnClient l s) (dnClient l s′) l₀ d₀ id₀ x crow)

dnIdlU-read : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
              (x : Payload)
            → phOf l s ≡ phOf l s′
            → LIC.CliRowP (dnLink l) hi (dnClient l s) (dnClient l s′)
                (output l₀ d₀ id₀) x
            → LBFD.DnIdl l s → LBFD.DnIdl l s′
dnIdlU-read l s s′ l₀ d₀ id₀ x deq crow =
  LBFD.dnIdl-read l s s′ x deq
    (LDB.cliRead-adj (dnLink l) hi (dnClient l s) (dnClient l s′) l₀ d₀ id₀ x crow)

------------------------------------------------------------------------
-- §5d  (T6c) THE CHAINSYNC HALF'S SELECTORS AND ITS `break` WRAPPER.
--
-- `LiveChanJoinCS` states every arm at its per-hop premises; since grant #12 each of
-- those premises IS a slot of the io cone or of `driverExpose⁺`, so all that is left
-- here is the SELECTION — one picker per (hop, axis), leg-dispatched for the reason
-- `rowsUp`/`csDrv` are.  The eight CS io slots arrive in three families: node A's two
-- UP-hop servers (`AllCssUpP`), the four CLIENTS (`AllCscP`, up-then-down in leg
-- order) and grant #11's two DOWN-hop servers (`AllCssP`, now PAIRED — the
-- label-directed half is `proj₂`).
------------------------------------------------------------------------

-- ONE `break` preserves both CS hops, at the assembly's own successor
chanCSLeg-break : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
                  (step : radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M)
                → LCC.ChanCSLeg l (toSys r)
                → LCC.ChanCSLeg l (toSys (proj₁ (LA.evStepJ-break l r l₀ step)))
chanCSLeg-break l r l₀ {a} step iv =
  let (m′ , _ , pheq , _ , _) = break-invert r l₀ {a} step
  in  LCJC.chanCSLeg-break l (toSys r) m′ pheq iv


-- the UP hop's api row PAIR, per leg: node A's server beside the relay's client.
-- *** STATED AT THE CONSTRUCTOR LEGS, not `_`-typed like `rowsUp`/`csDrv`. ***  Those
-- work because their result IS one of their arguments, so the call site solves the
-- meta; these COMBINE two record slots, and Agda cannot invert that (measured:
-- `[UnsolvedConstraints] Set = _1455 … (blocked on _1455)`).  The argument types ARE
-- `driverExpose⁺`'s own — `upLink legBD` is `linkAB` and `upCSsOf legBD s` is
-- `NodeStateA.csS-AB (nA s)` definitionally, which is exactly the conversion the leg
-- dispatch exists to make.
csApiUp : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
        → CSsApiRowP (upLink legBD) hi (LCC.upCSsOf legBD s) (LCC.upCSsOf legBD s′) e a
        → CSsApiRowP (upLink legCD) hi (LCC.upCSsOf legCD s) (LCC.upCSsOf legCD s′) e a
        → (CScApiRowP (upLink legBD) hi (LCC.upCScOf legBD s) (LCC.upCScOf legBD s′) e a × CSsApiRowP (dnLink legBD) hi (LCC.dnCSsOf legBD s) (LCC.dnCSsOf legBD s′) e a)
        → (CScApiRowP (upLink legCD) hi (LCC.upCScOf legCD s) (LCC.upCScOf legCD s′) e a × CSsApiRowP (dnLink legCD) hi (LCC.dnCSsOf legCD s) (LCC.dnCSsOf legCD s′) e a)
        → CSsApiRowP (upLink l) hi (LCC.upCSsOf l s) (LCC.upCSsOf l s′) e a
          × CScApiRowP (upLink l) hi (LCC.upCScOf l s) (LCC.upCScOf l s′) e a
csApiUp legBD s s′ e a srvBD srvCD rowsBD rowsCD = srvBD , proj₁ rowsBD
csApiUp legCD s s′ e a srvBD srvCD rowsBD rowsCD = srvCD , proj₁ rowsCD

-- … and the DOWN hop's: the relay's server beside node D's client
csApiDn : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
        → CScApiRowP (dnLink legBD) hi (LCC.dnCScOf legBD s) (LCC.dnCScOf legBD s′) e a
        → CScApiRowP (dnLink legCD) hi (LCC.dnCScOf legCD s) (LCC.dnCScOf legCD s′) e a
        → (CScApiRowP (upLink legBD) hi (LCC.upCScOf legBD s) (LCC.upCScOf legBD s′) e a × CSsApiRowP (dnLink legBD) hi (LCC.dnCSsOf legBD s) (LCC.dnCSsOf legBD s′) e a)
        → (CScApiRowP (upLink legCD) hi (LCC.upCScOf legCD s) (LCC.upCScOf legCD s′) e a × CSsApiRowP (dnLink legCD) hi (LCC.dnCSsOf legCD s) (LCC.dnCSsOf legCD s′) e a)
        → CSsApiRowP (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′) e a
          × CScApiRowP (dnLink l) hi (LCC.dnCScOf l s) (LCC.dnCScOf l s′) e a
csApiDn legBD s s′ e a cliBD cliCD rowsBD rowsCD = proj₂ rowsBD , cliBD
csApiDn legCD s s′ e a cliBD cliCD rowsBD rowsCD = proj₂ rowsCD , cliCD

-- the UP hop's io row pair, per leg (node A's server, the relay's client)
csIoUp : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
       → LIC.AllCssUpP s s′ e a → LIC.AllCscP s s′ e a
       → LIC.CssIoRowP (upLink l) hi (LCC.upCSsOf l s) (LCC.upCSsOf l s′) e a
         × LIC.CscIoRowP (upLink l) hi (LCC.upCScOf l s) (LCC.upCScOf l s′) e a
-- (`proj₂` on the server halves: `Csf` is the PAIR `CssPairP`, so the label-directed
-- fact the CS join's arms take is its second component — at the UP-hop servers too,
-- not only at grant #11's down-hop ones)
csIoUp legBD s s′ e a up csc = proj₂ (proj₁ up) , proj₁ csc
csIoUp legCD s s′ e a up csc = proj₂ (proj₂ up) , proj₁ (proj₂ csc)

-- … and the DOWN hop's (the relay's server — `proj₂` of the PAIR — and node D's client)
csIoDn : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
       → LIC.AllCssP s s′ e a → LIC.AllCscP s s′ e a
       → LIC.CssIoRowP (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′) e a
         × LIC.CscIoRowP (dnLink l) hi (LCC.dnCScOf l s) (LCC.dnCScOf l s′) e a
csIoDn legBD s s′ e a dn csc = proj₂ (proj₁ dn) , proj₁ (proj₂ (proj₂ csc))
csIoDn legCD s s′ e a dn csc = proj₂ (proj₂ dn) , proj₂ (proj₂ (proj₂ csc))

-- (T8c-iii) node D's PHASE across an io step, leg-selected off the io cone's own two
-- driver-slot fixities.  An io step touches no driver, so the content is entirely the
-- per-leg dispatch that makes `phOf` reduce
phFix : (l : TwoLegs) {s s′ : SysState}
      → NodeStateD.cons-BD (nD s) ≡ NodeStateD.cons-BD (nD s′)
      → NodeStateD.cons-CD (nD s) ≡ NodeStateD.cons-CD (nD s′)
      → phOf l s ≡ phOf l s′
phFix legBD bd cd = cong cph bd
phFix legCD bd cd = cong cph cd

------------------------------------------------------------------------
-- §5e  (T8c-iii) *** NODE D's FRESHNESS CLAUSE AND COUPLING, CARRIED — one lemma per
-- step class, all LEG-STATED. ***
--
-- The pair travels as ONE factor (`LiveDrvCSD.DnJoint`), so each arm below hands
-- `mkDnJoint` one `DnFresh` class and one `DrvCliD` class and nothing else: §5b's nine
-- wrappers and §5c's three ARE the proofs, and this section only routes them.
--
-- *** THE DISPATCHES, AND WHY EACH IS THE ONE IT IS. ***
--   · the two MEDIUM-only classes read the drained/broken key and nothing else, so
--     `drain-cell-at` (the CS join's own key dichotomy) decides them and the four
--     node-side slots are `refl` per leg;
--   · the api class dispatches on the two MERGED cone fields — `deRelay*` and
--     `deNodeD*` — because those are the only pair whose four combinations are all
--     realisable-or-carried.  `LiveDrvCSD` §8 (i-b)/(i-c) record why the separated
--     forms are not: each admits a combination no producer can build and no consumer
--     can refute;
--   · the two io classes mirror `LiveChanJoinCS.chanCSH-fill`/`-read` exactly, down to
--     the four peer shapes and the *(neither peer moved)* refutation — `csFill-noPeer-⊥`
--     and `csRead-noPeer-⊥` are reused verbatim, which is why this section transcribes
--     no table and no ownership argument of its own.
------------------------------------------------------------------------

-- the leg's two links are DISTINCT, per leg — what turns "the relay fired on its UP
-- link" into "the DOWN-hop CS server's row is impossible"
up≢dn : (l : TwoLegs) → upLink l ≡ dnLink l → ⊥
up≢dn legBD = linkAB≢linkBD
up≢dn legCD = linkAC≢linkCD

-- the four node-side slots the freshness clause reads, all `refl` under a MEDIUM-only
-- step (`PipeTauMed.drainSucc` and the `break` successor keep every node record
-- LITERAL, so the only content is the per-leg dispatch that makes the accessors reduce)
dnSlots-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
  → (relayOf l s ≡ relayOf l (drainSucc s i d₀ id₀))
    × (LCC.dnCSsOf l s ≡ LCC.dnCSsOf l (drainSucc s i d₀ id₀))
    × (LCC.dnCScOf l s ≡ LCC.dnCScOf l (drainSucc s i d₀ id₀))
    × (phOf l s ≡ phOf l (drainSucc s i d₀ id₀))
dnSlots-drain legBD s i d₀ id₀ = refl , refl , refl , refl
dnSlots-drain legCD s i d₀ id₀ = refl , refl , refl , refl

dnSlots-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
  → (relayOf l s ≡ relayOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
    × (LCC.dnCSsOf l s ≡ LCC.dnCSsOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
    × (LCC.dnCScOf l s ≡ LCC.dnCScOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
    × (phOf l s ≡ phOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
dnSlots-break legBD s m′ = refl , refl , refl , refl
dnSlots-break legCD s m′ = refl , refl , refl , refl

-- the FRAME, at the five slots the pair reads
dnJointU-frame : (l : TwoLegs) (s s′ : SysState)
               → relayOf l s ≡ relayOf l s′
               → LCC.dnCSsOf l s ≡ LCC.dnCSsOf l s′
               → LCC.cellCSDn l s ≡ LCC.cellCSDn l s′
               → LCC.dnCScOf l s ≡ LCC.dnCScOf l s′
               → phOf l s ≡ phOf l s′
               → LDC.DnJoint l s → LDC.DnJoint l s′
dnJointU-frame l s s′ peq seq heq keq deq =
  LDC.mkDnJoint l s s′ (LDC.dnFresh-frame l s s′ peq seq heq keq deq)
                       (LDC.drvCliD-frame l s s′ deq (cong coarsenCSc keq))
                       -- (T11e) the third half frames on the SAME five equations
                       (λ _ → LDC.dnRfw-frame l s s′ peq seq heq keq deq)

-- the `break` class: the medium's BROKEN bits only, so the cell rides one `cong`
dnJointU-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
               → phase m′ ≡ phase (med s)
               → LDC.DnJoint l s → LDC.DnJoint l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
dnJointU-break l s m′ pheq =
  let (peq , seq , keq , deq) = dnSlots-break l s m′
  in  dnJointU-frame l s _ peq seq
        (sym (cong (λ g → g (dnLink l) hi N2N_ChainSync) pheq)) keq deq

-- the medium-τ class: the drained key is this leg's own dn CS key — and then the cell
-- goes `draining x → empty`, which is §5b's own `dnFresh-drainS` — or it is another key
-- and the hop is framed.  The coupling reads no cell at all, so it frames either way
dnJointU-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                 (x : Payload)
               → phase (med s) i d₀ id₀ ≡ draining x
               → LDC.DnJoint l s → LDC.DnJoint l (drainSucc s i d₀ id₀)
dnJointU-drain l s i d₀ id₀ x drainEq
  with LCJC.drain-cell-at s i d₀ id₀ (dnLink l) hi N2N_ChainSync
... | inj₁ same =
      let (peq , seq , keq , deq) = dnSlots-drain l s i d₀ id₀
      in  dnJointU-frame l s _ peq seq (sym same) keq deq
... | inj₂ (refl , refl , refl , tgtEq) =
      let (peq , seq , keq , deq) = dnSlots-drain l s i d₀ id₀
      in  LDC.mkDnJoint l s _
            (LDC.dnFresh-drainS l s _ x peq drainEq tgtEq seq keq deq)
            (LDC.drvCliD-frame l s _ deq (cong coarsenCSc keq))
            -- (T11e) … and §6i's DRAIN, whose field-8 antecedent is `CellPreQ`
            -- precisely so this arm is a pure TRANSPORT
            (λ _ → LDC.dnRfw-drainS l s _ x peq drainEq tgtEq seq keq deq)

------------------------------------------------------------------------
-- §5f  (T8c-iii) THE api CLASS — the four-way dispatch, and the ONLY place the
-- which-node-fired question is asked.
------------------------------------------------------------------------

-- the api class.  `relayFired` and `nodeDFired` are the two MERGED cone fields at the
-- leg's own slots; `srow`/`crow` are the leg's dn-hop CS rows, already selected
dnJointU-api : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
               {e : Net_Api Payload X} {a : X}
             → med s ≡ med s′
             → (((relayOf l s ≡ relayOf l s′)
                 × (LCC.dnCSsOf l s ≡ LCC.dnCSsOf l s′))
                ⊎ (ApiHasLink (upLink l) e
                   ⊎ (Σ[ bb ∈ Block₃ ] Σ[ qq ∈ ProdPh ]
                        (relayOf l s′ ≡ producing bb qq) × (qq ≡ pp0 → ⊥))))
             → ((relayOf l s ≡ relayOf l s′)
                ⊎ LAC.RelayAdv (relayOf l s) (relayOf l s′))
             -- *** (T11e) THE CONE's node-D FIELD IS WIDER SINCE THE BF FOLD *** — it
             -- carries §2b⁷'s request landing and the `cp3` anchor's coarse source for
             -- node D's BlockFetch api class.  This arm reads NEITHER, so it takes the
             -- wide field and NARROWS it in one place rather than widening the ten
             -- local signatures below (`narrow`, in the `where` block)
             -- (T11h) … and WIDER STILL in its FIXITY arm: node D's dn BF CLIENT.  This
             -- arm reads it no more than it reads the two below, so `narrow` drops it
             → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′)
                 × (dnClient l s ≡ dnClient l s′))
                ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                      ─[ ev (evl (evLabel X e a)) ]─►
                      decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                   × ConsAdv (phOf l s) (phOf l s′)
                   × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                       (LCC.dnCScOf l s′) e a
                   × LAC.CliReqLand (dnLink l) hi (dnClient l s) (dnClient l s′) e a
                   × (phOf l s ≡ cp3
                      → Σ[ b″ ∈ Block₃ ]
                          (coarsenBFc (dnClient l s) ≡ NS.bcAblk b″))))
             → CSsApiRowP (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′) e a
             → CScApiRowP (dnLink l) hi (LCC.dnCScOf l s) (LCC.dnCScOf l s′) e a
             -- *** (T11e) THE THREE THINGS §6h's RECORD NEEDS AND THE OTHER TWO HALVES
             -- DO NOT. ***  The cone's `DnCsDrv` at THIS hop (its landing arm carries
             -- the `pp2` entry, the `pp3` landing and — since (T11c) — the relay's own
             -- ADVANCE, which is what closes the otherwise-unrefutable combination);
             -- the CARRIED token, whose `InCp03` the api class derives per state
             -- (review C-1); and the hop's ChainSync CHANNEL invariant at the
             -- SUCCESSOR, which is where the keystone reads `ccQui`/`ccPre`
             → LAC.DnCsDrv (dnLink l) (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′)
                           (relayOf l s) (relayOf l s′)
             → PipeInv l s
             → LCC.ChanCS (coarsenCSs (LCC.dnCSsOf l s′)) (LCC.cellCSDn l s′)
                          (LDC.dnCScC l s′)
             → LDC.DnJoint l s → LDC.DnJoint l s′
dnJointU-api l s s′ {X} {e} {a} medEq relayFired relayAdv nodeDFiredW srow crow
             csDrv pinv ivD′ =
  LDC.mkDnJoint l s s′ (freshHalf relayFired relayAdv nodeDFired) (cplHalf nodeDFired)
                       (λ cpl → rfwHalf cpl nodeDFired)
  where
  -- (T11e) the wide cone field, at the three components THIS arm reads
  -- an EXPLICIT dispatch and not a `with`: `with` on a variable bound in a parent
  -- clause is rejected, which is the banked reason `dnFresh⇒areq`'s `arms` idiom exists
  narrow : (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′)
             × (dnClient l s ≡ dnClient l s′))
            ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                  ─[ ev (evl (evLabel X e a)) ]─►
                  decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
               × ConsAdv (phOf l s) (phOf l s′)
               × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                   (LCC.dnCScOf l s′) e a
               × LAC.CliReqLand (dnLink l) hi (dnClient l s) (dnClient l s′) e a
               × (phOf l s ≡ cp3
                  → Σ[ b″ ∈ Block₃ ]
                      (coarsenBFc (dnClient l s) ≡ NS.bcAblk b″))))
         → ((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
           ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                 ─[ ev (evl (evLabel X e a)) ]─►
                 decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
              × ConsAdv (phOf l s) (phOf l s′)
              × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                  (LCC.dnCScOf l s′) e a)
  narrow (inj₁ (deq , keq , _))          = inj₁ (deq , keq)
  narrow (inj₂ (drv , cadv , fired , _)) = inj₂ (drv , cadv , fired)
  nodeDFired = narrow nodeDFiredW
  -- an api leaves the MEDIUM untouched, so this hop's CS cell is fixed by one `cong`
  cellEq : LCC.cellCSDn l s ≡ LCC.cellCSDn l s′
  cellEq = cong (λ m → phase m (dnLink l) hi N2N_ChainSync) medEq
  -- node D's joint adjacency, off §6c's producer.  Named because BOTH halves use it
  adjOf : (decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
             ─[ ev (evl (evLabel X e a)) ]─►
             decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
        → ConsAdv (phOf l s) (phOf l s′)
        → LDC.CliDrvAdj (LDC.dnCScC l s) (phOf l s) (LDC.dnCScC l s′) (phOf l s′)
  adjOf drvD cadv =
    LDC.cliDrvAdj-of (dnLink l) (cblkOf l s) (phOf l s) (phOf l s′)
      (LCC.dnCScOf l s) (LCC.dnCScOf l s′) drvD cadv crow
      (nodeDFiredSharp nodeDFired)
    where
    -- the sharpening, pulled out of whichever arm the field is in.  The FIXITY arm
    -- cannot reach here: `adjOf` is only ever applied under `inj₂`
    nodeDFiredSharp : (((phOf l s ≡ phOf l s′)
                        × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
                       ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                             ─[ ev (evl (evLabel X e a)) ]─►
                             decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                          × ConsAdv (phOf l s) (phOf l s′)
                          × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                              (LCC.dnCScOf l s′) e a))
                    → LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                        (LCC.dnCScOf l s′) e a
    nodeDFiredSharp (inj₁ (deq , keq)) = λ p → ⊥-elim (LDC.consAdv-irr (phOf l s)
                                                 (subst (ConsAdv (phOf l s)) (sym deq) cadv))
    nodeDFiredSharp (inj₂ (_ , _ , fired)) = fired
  -- *** THE COUPLING's HALF. ***  it frames when node D did not fire and rides §6c's
  -- producer when it did.  The dispatch is on an EXPLICIT argument, not a `with`:
  -- `with` on a variable bound in a parent clause is rejected, and this is
  -- `LiveDrvCSD.dnFresh⇒areq`'s own `arms` idiom
  cplHalf : (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
             ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                   ─[ ev (evl (evLabel X e a)) ]─►
                   decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                × ConsAdv (phOf l s) (phOf l s′)
                × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                    (LCC.dnCScOf l s′) e a))
          → LDC.DrvCliD l s → LDC.DrvCliD l s′
  cplHalf (inj₁ (deq , keq)) = LDC.drvCliD-frame l s s′ deq (cong coarsenCSc keq)
  cplHalf (inj₂ (drvD , cadv , fired)) =
    LDC.drvCliD-api l s s′
      (LDC.cliDrvAdj-of (dnLink l) (cblkOf l s) (phOf l s) (phOf l s′)
         (LCC.dnCScOf l s) (LCC.dnCScOf l s′) drvD cadv crow fired)
  -- *** THE FRESHNESS CLAUSE's HALF — the four-way dispatch, all on explicit
  -- arguments. ***  The relay's own advance is read only where it is needed: on the
  -- UP-link branch, where the guard has to be transported rather than discarded
  relayIn : (b : Block₃) (c : ConsPh) → relayOf l s ≡ consuming b c
          → LCC.dnCSsOf l s ≡ LCC.dnCSsOf l s′
          → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
             ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                   ─[ ev (evl (evLabel X e a)) ]─►
                   decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                × ConsAdv (phOf l s) (phOf l s′)
                × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                    (LCC.dnCScOf l s′) e a))
          → LDC.DnFresh l s → LDC.DnFresh l s′
  relayIn b c req seq (inj₁ (deq , keq)) =
    LDC.dnFresh-relayCons l s s′ b c req seq cellEq keq deq
  relayIn b c req seq (inj₂ (drvD , cadv , fired)) =
    LDC.dnFresh-relayConsApi l s s′ b c req seq cellEq (adjOf drvD cadv)
  -- the relay's phase is FIXED (either arm's fixity half): frame or node D's class
  relayFix : relayOf l s ≡ relayOf l s′
           → LCC.dnCSsOf l s ≡ LCC.dnCSsOf l s′
           → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
              ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                    ─[ ev (evl (evLabel X e a)) ]─►
                    decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                 × ConsAdv (phOf l s) (phOf l s′)
                 × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                     (LCC.dnCScOf l s′) e a))
           → LDC.DnFresh l s → LDC.DnFresh l s′
  relayFix peq seq (inj₁ (deq , keq)) =
    LDC.dnFresh-frame l s s′ peq seq cellEq keq deq
  relayFix peq seq (inj₂ (drvD , cadv , fired)) =
    LDC.dnFresh-nodeDApi l s s′ peq seq cellEq (adjOf drvD cadv)
  -- the dn CS SERVER's fixity, off the fired link
  srvFix : ApiHasLink (upLink l) e → LCC.dnCSsOf l s ≡ LCC.dnCSsOf l s′
  srvFix ahl =
    LDC.cssRowP-noLink (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′)
      _ _ ahl (up≢dn l) srow
  -- the UP-link branch: the server's row is refuted BY LINK, then the relay's own
  -- advance decides between the fixed, the in-region and the outside classes
  relayUp : ApiHasLink (upLink l) e
          → ((relayOf l s ≡ relayOf l s′)
             ⊎ LAC.RelayAdv (relayOf l s) (relayOf l s′))
          → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
             ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                   ─[ ev (evl (evLabel X e a)) ]─►
                   decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                × ConsAdv (phOf l s) (phOf l s′)
                × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                    (LCC.dnCScOf l s′) e a))
          → LDC.DnFresh l s → LDC.DnFresh l s′
  relayUp ahl (inj₁ peq) nd = relayFix peq (srvFix ahl) nd
  relayUp ahl (inj₂ raL) nd = guarded (LDC.relayAdv-guard _ _ raL) nd
    where
    guarded : ((Σ[ b ∈ Block₃ ] Σ[ c ∈ ConsPh ] (relayOf l s ≡ consuming b c))
               ⊎ (LDC.RelayFresh (relayOf l s′) → ⊥))
            → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
               ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                     ─[ ev (evl (evLabel X e a)) ]─►
                     decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                  × ConsAdv (phOf l s) (phOf l s′)
                  × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                      (LCC.dnCScOf l s′) e a))
            → LDC.DnFresh l s → LDC.DnFresh l s′
    guarded (inj₂ nof) _ = LDC.dnFresh-relayOut l s s′ nof
    guarded (inj₁ (b , c , req)) nd′ = relayIn b c req (srvFix ahl) nd′
  freshHalf : (((relayOf l s ≡ relayOf l s′)
                × (LCC.dnCSsOf l s ≡ LCC.dnCSsOf l s′))
               ⊎ (ApiHasLink (upLink l) e
                  ⊎ (Σ[ bb ∈ Block₃ ] Σ[ qq ∈ ProdPh ]
                       (relayOf l s′ ≡ producing bb qq) × (qq ≡ pp0 → ⊥))))
            → ((relayOf l s ≡ relayOf l s′)
               ⊎ LAC.RelayAdv (relayOf l s) (relayOf l s′))
            → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
               ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                     ─[ ev (evl (evLabel X e a)) ]─►
                     decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                  × ConsAdv (phOf l s) (phOf l s′)
                  × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                      (LCC.dnCScOf l s′) e a))
            → LDC.DnFresh l s → LDC.DnFresh l s′
  freshHalf (inj₁ (peq , seq)) _ nd = relayFix peq seq nd
  freshHalf (inj₂ (inj₁ ahl)) ra nd = relayUp ahl ra nd
  freshHalf (inj₂ (inj₂ (bb , qq , peq′ , nz))) _ _ =
    LDC.dnFresh-relayOut l s s′
      (λ g → LDC.relayFresh-prod-nz bb qq nz (subst LDC.RelayFresh peq′ g))

  -- *** (T11e) §6h's RECORD AT THE api CLASS — §6i(c)'s five-arm dispatch, and it
  -- needs NEITHER the fired link nor the server's fixity. ***  Dispatch the GUARD at
  -- the SUCCESSOR first (both the keystone and the in-guard advance are stated there),
  -- then the cone's `DnCsDrv`:
  --
  --   · `pp2`, LANDING arm → the keystone REBUILDS the record from `DnCsAwLand`'s
  --     `csWar` plus `ccQui`/`ccPre` at the successor.  It does not matter what node D
  --     did, nor which link fired: on an up-link arm the landing is refuted BY THE
  --     LINK inside the cone's own producer and the case is vacuous.
  --   · `pp3`, LANDING arm → the fourth member's `RelayAdv` gives the SOURCE phase
  --     (`relayAdv-into-pp3`) and the third landing gives the server; node D's own
  --     move composes in front (`dnRfw-relayAdvJ`) or frames (`dnRfw-relayAdvC`).
  --   · FIXITY arm (either phase) → relay AND server fixed, so the guard transports
  --     backwards: frame, or §6i's node-D api class with the token.
  --   · guard `⊥` at the successor → `dnRfw-out`, and nothing else is read.
  --
  -- (F105  *** THE GUARD's TWO ENDS ARE NOT INTERCHANGEABLE — §6g's postscript, at
  -- the carry. ***)  swap the two landing branches so the KEYSTONE is fed the `pp3`
  -- equation and the in-guard advance the `pp2` one (arity-preserving; the clause set
  -- is untouched).  *** RED ***: `LiveChanJoin.agda:1435.30-34: [UnequalTerms] pp3 !=
  -- pp2 of type ProdPh … when checking that the expression peq′ has type relayOf l s′
  -- ≡ producing b pp2`, EXIT=42 — the entering step is the `pp1 → pp2` hop and the
  -- advance is `pp2 → pp3`; reading the region's left end as its right one is exactly
  -- the shape F97 refutes one layer down.  Reverted by string inversion, `git status`
  -- clean after.
  rfwHalf : LDC.DrvCliD l s
          → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
             ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                   ─[ ev (evl (evLabel X e a)) ]─►
                   decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                × ConsAdv (phOf l s) (phOf l s′)
                × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                    (LCC.dnCScOf l s′) e a))
          → LDC.DnRfw l s → LDC.DnRfw l s′
  rfwHalf cpl nd rw g′ = arms (LDC.relayRfw-cases (relayOf l s′) g′) csDrv nd rw g′
    where
    -- the FIXITY arm, at either phase: the relay and the server both held
    fixed : relayOf l s ≡ relayOf l s′
          → LCC.dnCSsOf l s ≡ LCC.dnCSsOf l s′
          → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
             ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                   ─[ ev (evl (evLabel X e a)) ]─►
                   decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
                × ConsAdv (phOf l s) (phOf l s′)
                × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                    (LCC.dnCScOf l s′) e a))
          → LDC.DnRfw l s → LDC.DnRfw l s′
    fixed peq seq (inj₁ (deq , keq)) =
      LDC.dnRfw-frame l s s′ peq seq cellEq keq deq
    fixed peq seq (inj₂ (drvD , cadv , fired)) =
      LDC.dnRfw-nodeDApi l s s′ peq seq cellEq
        (LDC.pipeInv⇒inCp03 l s (subst LDC.RelayRfw (sym peq) g″) pinv)
        (adjOf drvD cadv)
      where
      -- the guard at the SOURCE, transported back along the relay's own fixity — it
      -- is what makes the token's projection applicable here
      g″ : LDC.RelayRfw (relayOf l s′)
      g″ = g′
    arms : (Σ[ b ∈ Block₃ ] relayOf l s′ ≡ producing b pp2)
           ⊎ (Σ[ b ∈ Block₃ ] relayOf l s′ ≡ producing b pp3)
         → LAC.DnCsDrv (dnLink l) (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′)
                       (relayOf l s) (relayOf l s′)
         → (((phOf l s ≡ phOf l s′) × (LCC.dnCScOf l s ≡ LCC.dnCScOf l s′))
            ⊎ ((decConsD (dnLink l) (consD (cblkOf l s) (phOf l s))
                  ─[ ev (evl (evLabel X e a)) ]─►
                  decConsD (dnLink l) (consD (cblkOf l s′) (phOf l s′)))
               × ConsAdv (phOf l s) (phOf l s′)
               × LAC.CscCliFired (dnLink l) hi (LCC.dnCScOf l s)
                   (LCC.dnCScOf l s′) e a))
         → LDC.DnRfw l s → LDC.DnRfw l s′
    arms _ (inj₁ (peq , seq)) nd′ rw′ = fixed peq seq nd′ rw′
    -- `pp2`: the KEYSTONE, and it reads only successor-side facts
    arms (inj₁ (b , peq′)) (inj₂ (_ , awLand , _ , _)) _ _ =
      LDC.dnRfw-enter l s′ b peq′ (awLand b peq′)
        (LCC.ccQui ivD′ (subst LCC.SrvPre (sym (awLand b peq′)) tt))
        (LCC.ccPre ivD′ (subst LCC.SrvPre (sym (awLand b peq′)) tt))
        (cplHalf nd cpl)
    -- `pp3`: the in-guard ADVANCE, with node D's own move composed in front when the
    -- cone reports it fired too
    arms (inj₂ (b , peq′)) (inj₂ (_ , _ , rfwLand , raC)) (inj₁ (deq , keq)) rw′ =
      LDC.dnRfw-relayAdvC l s s′ b (dnLink l)
        (LDC.relayAdv-into-pp3 b raC peq′) peq′
        (λ bb eq → rfwLand bb eq) cellEq keq deq rw′
    arms (inj₂ (b , peq′)) (inj₂ (_ , _ , rfwLand , raC))
         (inj₂ (drvD , cadv , fired)) rw′ =
      LDC.dnRfw-relayAdvJ l s s′ b (proj₁ (rfwLand b peq′))
        (LDC.relayAdv-into-pp3 b raC peq′) peq′ (proj₂ (rfwLand b peq′)) cellEq
        (LDC.pipeInv⇒inCp03 l s
           (LDC.relayRfw-pp2 l s b (LDC.relayAdv-into-pp3 b raC peq′)) pinv)
        (adjOf drvD cadv) rw′

------------------------------------------------------------------------
-- §5g  (T8c-iii) THE TWO io CLASSES — `LiveChanJoinCS.chanCSH-fill`/`-read`'s
-- structure at this invariant, down to the four peer shapes and the *(neither peer
-- moved)* refutation.  Both refutations (`csSend-⊥`/`csRead-⊥` for the payload's role,
-- `csFill-noPeer-⊥`/`csRead-noPeer-⊥` for the ownership certificates) are REUSED
-- verbatim, which is why this section transcribes no table of its own.
--
-- The coupling reads no cell at all, so its half is `drvCliD-frame` on every shape but
-- the client's own write, where it is `drvCliD-send`/`-read`.
--
-- *** KEEP IN SYNC WITH `LiveChanJoinCS.chanCSH-fill`/`-read` — SCOPED, and the scope is
-- the point. ***  What must stay in sync is the STRUCTURE: the `setRead⁺` key dichotomy,
-- the four peer shapes in that order, and which refutation closes each of the last two.
-- What must NOT be copied is the frame's cell ORIENTATION: this invariant's frame takes
-- the cell equation `s → s′` and the CS channel's takes it `s′ → s`, so the off-key
-- branches here carry a `sym` that its counterpart does not.  *** F77 is the guard on
-- exactly that difference *** (§5h) — dropping the `sym` to match the sibling goes RED.
-- A sync sweep that "tidies" the `sym` away is the one edit this marker exists to stop.
------------------------------------------------------------------------

-- the io FILL class
dnJointU-fill : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
                (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (full x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ empty
  → relayOf l s ≡ relayOf l s′
  → phOf l s ≡ phOf l s′
  → LIC.CssIoRowP (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′) (input l₀ d₀ id₀) x
  → LIC.CscIoRowP (dnLink l) hi (LCC.dnCScOf l s) (LCC.dnCScOf l s′) (input l₀ d₀ id₀) x
  → LDC.DnJoint l s → LDC.DnJoint l s′
dnJointU-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty peq deq srow crow
  with LCJC.setRead⁺ (phase (med s)) l₀ d₀ id₀ (full x) (dnLink l) hi N2N_ChainSync
-- AWAY from this hop's key: the hop is framed and neither row can be inhabited
... | inj₁ (miss , same) =
      dnJointU-frame l s s′ peq
        (LCJC.cssRow-off (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′)
           l₀ d₀ id₀ x miss srow)
        -- the frame wants `s → s′`; `setRead⁺`'s off-key answer and `sEq` compose the
        -- other way round, exactly as `chanCSH-fill`'s own call does
        (sym (trans (cong (λ m → phase m (dnLink l) hi N2N_ChainSync) sEq) (sym same)))
        (LCJC.cscRow-off (dnLink l) hi (LCC.dnCScOf l s) (LCC.dnCScOf l s′)
           l₀ d₀ id₀ x miss crow)
        deq
-- AT this hop's key: the cell filled, so exactly one of its two peers moved
... | inj₂ (refl , refl , refl , tgt) = hit srow crow
  where
  cellSrc : LCC.cellCSDn l s ≡ empty
  cellSrc = srcEmpty
  cellTgt : LCC.cellCSDn l s′ ≡ full x
  cellTgt = trans (cong (λ m → phase m (dnLink l) hi N2N_ChainSync) sEq) tgt
  hit : LIC.CssIoRowP (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′)
          (input (dnLink l) hi N2N_ChainSync) x
      → LIC.CscIoRowP (dnLink l) hi (LCC.dnCScOf l s) (LCC.dnCScOf l s′)
          (input (dnLink l) hi N2N_ChainSync) x
      → LDC.DnJoint l s → LDC.DnJoint l s′
  -- the SERVER wrote: its five rows all START outside `SrvFresh`, so §5's own class
  -- refutes the step by the server conjunct alone and the cell is never read
  hit (inj₂ srowEq) (inj₁ (ceq , _)) =
    LDC.mkDnJoint l s s′
      (LDC.dnFresh-srvSendS l s s′ x peq cellSrc cellTgt ceq deq
        (LCC.srvSendRow (dnLink l) hi (coarsenCSs (LCC.dnCSsOf l s)) x
          (coarsenCSs (LCC.dnCSsOf l s′)) srowEq))
      (LDC.drvCliD-frame l s s′ deq (cong coarsenCSc ceq))
      -- (T11e) … and §6i's server FILL, the class that ESTABLISHES both of the
      -- record's cell⇒client correlations
      (λ _ → LDC.dnRfw-srvSendS l s s′ x peq cellSrc cellTgt ceq deq
        (LCC.srvSendRow (dnLink l) hi (coarsenCSs (LCC.dnCSsOf l s)) x
          (coarsenCSs (LCC.dnCSsOf l s′)) srowEq))
  -- … or the CLIENT did — and its REQUEST row is the one step that ESTABLISHES the
  -- freshness clause's correlation
  hit (inj₁ (seq , _)) (inj₂ crowEq) =
    LDC.mkDnJoint l s s′
      (LDC.dnFresh-cliSendS l s s′ x peq cellSrc cellTgt seq deq
        (LCC.cliSendRow (dnLink l) hi (coarsenCSc (LCC.dnCScOf l s)) x
          (coarsenCSc (LCC.dnCScOf l s′)) crowEq))
      (LDC.drvCliD-send l s s′ x deq
        (LCC.cliSendRow (dnLink l) hi (coarsenCSc (LCC.dnCScOf l s)) x
          (coarsenCSc (LCC.dnCScOf l s′)) crowEq))
      -- (T11e) … and §6i's client class, THIRD as `mkDnJoint` orders its halves
      (λ _ → LDC.dnRfw-cliSendS l s s′ x peq cellSrc cellTgt seq deq
        (LCC.cliSendRow (dnLink l) hi (coarsenCSc (LCC.dnCScOf l s)) x
          (coarsenCSc (LCC.dnCScOf l s′)) crowEq))
  -- BOTH would have written the SAME payload: impossible by its ROLE
  hit (inj₂ srowEq) (inj₂ crowEq) =
    ⊥-elim (LCJC.csSend-⊥
             (LCC.srvSendRow (dnLink l) hi (coarsenCSs (LCC.dnCSsOf l s)) x
               (coarsenCSs (LCC.dnCSsOf l s′)) srowEq)
             (LCC.cliSendRow (dnLink l) hi (coarsenCSc (LCC.dnCScOf l s)) x
               (coarsenCSc (LCC.dnCScOf l s′)) crowEq))
  -- NEITHER moved while the cell filled: the two ownership certificates decide it
  hit (inj₁ (_ , nsrv)) (inj₁ (_ , ncli)) =
    ⊥-elim (LCJC.csFill-noPeer-⊥ (dnLink l) hi x
             (LCJC.role-in (dnLink l) hi N2N_ChainSync x) nsrv ncli)

-- … and the io READ class, the same four shapes at the other polarity
dnJointU-read : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
                (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (draining x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ full x
  → relayOf l s ≡ relayOf l s′
  → phOf l s ≡ phOf l s′
  → LIC.CssIoRowP (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′) (output l₀ d₀ id₀) x
  → LIC.CscIoRowP (dnLink l) hi (LCC.dnCScOf l s) (LCC.dnCScOf l s′) (output l₀ d₀ id₀) x
  → LDC.DnJoint l s → LDC.DnJoint l s′
dnJointU-read l s s′ l₀ d₀ id₀ x sEq srcFull peq deq srow crow
  with LCJC.setRead⁺ (phase (med s)) l₀ d₀ id₀ (draining x) (dnLink l) hi N2N_ChainSync
... | inj₁ (miss , same) =
      dnJointU-frame l s s′ peq
        (LCJC.cssRowR-off (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′)
           l₀ d₀ id₀ x miss srow)
        -- the frame wants `s → s′`; `setRead⁺`'s off-key answer and `sEq` compose the
        -- other way round, exactly as `chanCSH-fill`'s own call does
        (sym (trans (cong (λ m → phase m (dnLink l) hi N2N_ChainSync) sEq) (sym same)))
        (LCJC.cscRowR-off (dnLink l) hi (LCC.dnCScOf l s) (LCC.dnCScOf l s′)
           l₀ d₀ id₀ x miss crow)
        deq
... | inj₂ (refl , refl , refl , tgt) = hit srow crow
  where
  cellSrc : LCC.cellCSDn l s ≡ full x
  cellSrc = srcFull
  cellTgt : LCC.cellCSDn l s′ ≡ draining x
  cellTgt = trans (cong (λ m → phase m (dnLink l) hi N2N_ChainSync) sEq) tgt
  hit : LIC.CssIoRowP (dnLink l) hi (LCC.dnCSsOf l s) (LCC.dnCSsOf l s′)
          (output (dnLink l) hi N2N_ChainSync) x
      → LIC.CscIoRowP (dnLink l) hi (LCC.dnCScOf l s) (LCC.dnCScOf l s′)
          (output (dnLink l) hi N2N_ChainSync) x
      → LDC.DnJoint l s → LDC.DnJoint l s′
  -- the SERVER read: this is the step the arms' own equation names — it lands at
  -- `csAreq`, INSIDE the fresh region, with the cell `draining`
  hit (inj₂ srowEq) (inj₁ (ceq , _)) =
    LDC.mkDnJoint l s s′
      (LDC.dnFresh-srvReadS l s s′ x peq cellSrc cellTgt ceq deq
        (LCC.srvReadRow (dnLink l) hi (coarsenCSs (LCC.dnCSsOf l s)) x
          (coarsenCSs (LCC.dnCSsOf l s′)) srowEq))
      (LDC.drvCliD-frame l s s′ deq (cong coarsenCSc ceq))
      -- (T11e) … and §6i's server READ, whose three rows the cell region refutes
      (λ _ → LDC.dnRfw-srvReadS l s s′ x peq cellSrc cellTgt ceq deq
        (LCC.srvReadRow (dnLink l) hi (coarsenCSs (LCC.dnCSsOf l s)) x
          (coarsenCSs (LCC.dnCSsOf l s′)) srowEq))
  -- … or the CLIENT read, and all seven of its rows are refuted by §5's own class
  hit (inj₁ (seq , _)) (inj₂ crowEq) =
    LDC.mkDnJoint l s s′
      (LDC.dnFresh-cliReadS l s s′ x peq cellSrc cellTgt seq deq
        (LCC.cliReadRow (dnLink l) hi (coarsenCSc (LCC.dnCScOf l s)) x
          (coarsenCSc (LCC.dnCScOf l s′)) crowEq))
      (LDC.drvCliD-read l s s′ x deq
        (LCC.cliReadRow (dnLink l) hi (coarsenCSc (LCC.dnCScOf l s)) x
          (coarsenCSc (LCC.dnCScOf l s′)) crowEq))
      -- (T11e) … and §6i's client class, THIRD as `mkDnJoint` orders its halves
      (λ _ → LDC.dnRfw-cliReadS l s s′ x peq cellSrc cellTgt seq deq
        (LCC.cliReadRow (dnLink l) hi (coarsenCSc (LCC.dnCScOf l s)) x
          (coarsenCSc (LCC.dnCScOf l s′)) crowEq))
  hit (inj₂ srowEq) (inj₂ crowEq) =
    ⊥-elim (LCJC.csRead-⊥
             (LCC.srvReadRow (dnLink l) hi (coarsenCSs (LCC.dnCSsOf l s)) x
               (coarsenCSs (LCC.dnCSsOf l s′)) srowEq)
             (LCC.cliReadRow (dnLink l) hi (coarsenCSc (LCC.dnCScOf l s)) x
               (coarsenCSc (LCC.dnCScOf l s′)) crowEq))
  hit (inj₁ (_ , nsrv)) (inj₁ (_ , ncli)) =
    ⊥-elim (LCJC.csRead-noPeer-⊥ (dnLink l) hi x
             (LCJC.role-out (dnLink l) hi N2N_ChainSync x) nsrv ncli)

-- (T8c-iii) … and node D's pair across the same `break`, the same three lines
-- (T11h) the freshness half's `break` wrapper, `dnJointU-break-at`'s shape exactly
bfFreshU-break-at : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
                    (step : radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M)
                  → LBFD.BFFresh l (toSys r)
                  → LBFD.BFFresh l (toSys (proj₁ (LA.evStepJ-break l r l₀ step)))
bfFreshU-break-at l r l₀ {a} step fr =
  let (m′ , _ , pheq , _ , _) = break-invert r l₀ {a} step
  in  bfFreshU-break l (toSys r) m′ pheq fr

-- (B, cellCp3) … and the third member's, which needs no cell equation at all
dnIdlU-break-at : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
                  (step : radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M)
                → LBFD.DnIdl l (toSys r)
                → LBFD.DnIdl l (toSys (proj₁ (LA.evStepJ-break l r l₀ step)))
dnIdlU-break-at l r l₀ {a} step di =
  dnIdlU-break l (toSys r) (proj₁ (break-invert r l₀ {a} step)) di

dnJointU-break-at : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
                    (step : radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M)
                  → LDC.DnJoint l (toSys r)
                  → LDC.DnJoint l (toSys (proj₁ (LA.evStepJ-break l r l₀ step)))
dnJointU-break-at l r l₀ {a} step dn =
  let (m′ , _ , pheq , _ , _) = break-invert r l₀ {a} step
  in  dnJointU-break l (toSys r) m′ pheq dn

------------------------------------------------------------------------
-- §5h  (T8c-iii) THE CARRY's OWN GUARDS — THREE, one per novel family of §§5e-5g:
-- the io frame's ORIENTATION, the two io arms' POLARITY, and the api dispatch's LINK
-- reasoning.  All arity-preserving, all RUN, all RED, all reverted by STRING
-- INVERSION with `git status` verified clean after each.  As-run at `6a17e33`.
--
-- (F77  *** THE io FRAME's ORIENTATION. ***)  drop the `sym` from §5g's off-key cell
--      equation in the FILL arm — i.e. hand the frame the composition
--      `chanCSLeg-fill`'s own call produces.  Arity-preserving and it is the mutation
--      a reader syncing the two sections would make, because the CS channel's frame
--      really does want the other direction.  *** RED ***
--      `LiveChanJoin.agda:1352.17-69: error: [UnequalTerms] phase (med s′) (dnLink l)
--      hi N2N_ChainSync != phase (med s) (dnLink l) hi N2N_ChainSync of type
--      CopyPhase`.  What it establishes: the two invariants' frames take their cell
--      equation in OPPOSITE directions, so the sections cannot be copied between each
--      other without the `sym` — the one place §5g is not a transcription.
--
-- (F78  *** THE TWO io ARMS' POLARITY. ***)  give the READ arm the FILL arm's off-key
--      helpers (`cssRow-off`/`cscRow-off` for `cssRowR-off`/`cscRowR-off`).
--      Arity-preserving, and the four names differ by one letter.  *** RED ***
--      `LiveChanJoin.agda:1415.29-33: error: [UnequalTerms] (output l₀ d₀ id₀) !=
--      (input l₀ d₀ id₀) …`.  What it establishes: the off-key refutations are
--      polarity-SPECIFIC — this is F72's finding at the join layer, and it is why
--      `LiveChanJoinCS` keeps four lemmas where two would look sufficient.
--
-- (F79  *** THE api DISPATCH's LINK REASONING — the sharpest of the three. ***)  aim
--      §5f's `srvFix` at the UP hop (`cssRowP-noLink (upLink l) …`) instead of the
--      DOWN one.  Arity-preserving, and genuinely tempting: the branch's hypothesis IS
--      `ApiHasLink (upLink l) e`, so the up link is the one in the reader's head.
--      *** RED ***  `LiveChanJoin.agda:1270.16-23: error: [UnequalTerms] upLink l !=
--      dnLink l of type Fin (numLinks p) when checking that the expression up≢dn l has
--      type upLink l ≡ upLink l → ⊥`.  *** What it establishes is the whole content of
--      the branch: *** the fired link and the PEER's key must be DIFFERENT for the
--      refutation to say anything, and aiming the pin at the fired link collapses the
--      disequality into `x ≡ x → ⊥`.  The error names that collapse literally.
--
-- *** RE-AIMING NOTES. ***  F77 dies if the two frames are ever unified (then the
-- merged frame is a new family and wants its own guard); F78 dies only if the four
-- off-key helpers are made polarity-generic; F79 is aimed at the api dispatch's
-- up-link branch and must be re-aimed, not deleted, if that branch is ever split by
-- hop.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §5i  (T10) THE UP-HOP PAIR's OWN DATA.  Three one-liners and two dispatches: the
-- `cp4` region's arms want the leg's up cell in the MEDIUM form, node A's two slots'
-- fixity, and — at the io classes — the same key dispatch `chanH-fill`/`chanH-read`
-- perform, with the WRITER (resp. the reader's row) KEPT.
------------------------------------------------------------------------

-- (the leg's UP cell in its MEDIUM form is the BANKED `PipeTauIo.cellUp-key`, the
-- same term `HUp`'s instantiation feeds `HopArm` — reused rather than restated, and
-- a local twin would not be convertible with the hop module's own parameter)

-- an EMPTY cell holds no unread block
emptyNotBlk : LLI.CellFullBlk empty → ⊥
emptyNotBlk ()

-- node A's two driver slots, per leg (the io cone reports them at positions 7-8)
-- (`_`-typed, the file's own leg-dispatch idiom: the two sides are the io cone's
-- node-PROJECTION form and the coupling's `prodOf` form, and spelling either out
-- here would fix the one this dispatch exists to convert between — review M-5)
prodFix-of : (l : TwoLegs) (s s′ : SysState)
           → prodOf legBD s ≡ prodOf legBD s′
           → prodOf legCD s ≡ prodOf legCD s′
           → prodOf l s ≡ prodOf l s′
prodFix-of legBD s s′ ab ac = ab
prodFix-of legCD s s′ ab ac = ac

-- … and all four slots across a MEDIUM-ONLY successor (the `break` shape, where every
-- node record is a literal)
upMed-fix : (l : TwoLegs) (s : SysState) (m′ : MedState)
          → (prodOf   l s ≡ prodOf   l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
          × (relayOf  l s ≡ relayOf  l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
          × (upClient l s ≡ upClient l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
          × (upSrv    l s ≡ upSrv    l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
upMed-fix legBD s m′ = refl , refl , refl , refl
upMed-fix legCD s m′ = refl , refl , refl , refl

-- the DRAIN's cell datum: the drained key is this hop's own — and then the cell is
-- `empty`, which holds no block — or it is another key and the cell is fixed
upCellDrain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
            → (cellUp l s ≡ cellUp l (drainSucc s i d₀ id₀))
              ⊎ (LLI.CellFullBlk (cellUp l (drainSucc s i d₀ id₀)) → ⊥)
upCellDrain l s i d₀ id₀ with drain-cell-at s i d₀ id₀ (upLink l) hi N2N_BlockFetch
... | inj₁ same =
      inj₁ (trans (cellUp-key l s)
                  (trans (sym same) (sym (cellUp-key l (drainSucc s i d₀ id₀)))))
... | inj₂ (_ , _ , _ , tgt) =
      inj₂ (λ hc → emptyNotBlk
              (subst LLI.CellFullBlk
                     (trans (cellUp-key l (drainSucc s i d₀ id₀)) tgt) hc))

-- the io FILL's two data, off ONE key dispatch: the cell (paired with its WRITER at
-- the hit) and the client's own row.  `chanH-fill`'s four hit shapes, verbatim —
-- including the two impossible ones (`srvSend-cliSend-⊥` and the ownership pair)
upFillData : (l : TwoLegs) (s s′ : SysState)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (full x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ empty
  → LIC.SrvRowP (upLink l) hi (upSrv l s) (upSrv l s′) (input l₀ d₀ id₀) x
  → LIC.CliRowP (upLink l) hi (upClient l s) (upClient l s′) (input l₀ d₀ id₀) x
  → ((cellUp l s ≡ cellUp l s′)
     ⊎ ((cellUp l s′ ≡ full x)
        × (LCI.SrvSendAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′))
           ⊎ LCI.CliSendAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′)))))
    × ((coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
       ⊎ LCI.CliSendAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′)))
upFillData l s s′ l₀ d₀ id₀ x sEq srcEmpty srow crow
  with setRead⁺ (phase (med s)) l₀ d₀ id₀ (full x) (upLink l) hi N2N_BlockFetch
... | inj₁ (miss , same) =
      inj₁ (trans (cellUp-key l s)
              (trans same
                (trans (sym (cong (λ m → phase m (upLink l) hi N2N_BlockFetch) sEq))
                       (sym (cellUp-key l s′)))))
    , inj₁ (cong coarsenBFc
              (cliRow-off (upLink l) hi (upClient l s) (upClient l s′)
                          l₀ d₀ id₀ x miss crow))
-- AT the hop's key: the cell filled, so exactly one of its peers wrote it.  The row
-- dispatch is NESTED `with`s and not a typed helper: the hit's three equations
-- orient the hop's key on the LEFT, so a helper declared at either key fails to
-- match the rows in the context (measured: `[UnequalTerms] … != (Lift ⊤)` at the
-- ownership certificate)
... | inj₂ (refl , refl , refl , tgt) with srow | crow
-- the SERVER wrote: its row is the adjacency, the client is fixed
...   | inj₂ (refl , refl , srowEq) | inj₁ (ceq , _) =
        inj₂ ( trans (cellUp-key l s′)
                 (trans (cong (λ m → phase m (upLink l) hi N2N_BlockFetch) sEq) tgt)
             , inj₁ (LCI.srvSendRow (upLink l) hi (coarsenBFs (upSrv l s)) x
                       (coarsenBFs (upSrv l s′)) srowEq) )
      , inj₁ (cong coarsenBFc ceq)
-- … or the CLIENT did, and the server is fixed
...   | inj₁ (seq , _) | inj₂ (refl , refl , crowEq) =
        inj₂ ( trans (cellUp-key l s′)
                 (trans (cong (λ m → phase m (upLink l) hi N2N_BlockFetch) sEq) tgt)
             , inj₂ (LCI.cliSendRow (upLink l) hi (coarsenBFc (upClient l s)) x
                       (coarsenBFc (upClient l s′)) crowEq) )
      , inj₂ (LCI.cliSendRow (upLink l) hi (coarsenBFc (upClient l s)) x
                (coarsenBFc (upClient l s′)) crowEq)
-- BOTH would have written the same payload: impossible by its role
...   | inj₂ (refl , refl , srowEq) | inj₂ (refl , refl , crowEq) =
        ⊥-elim (LCI.srvSend-cliSend-⊥
                  (LCI.srvSendRow (upLink l) hi (coarsenBFs (upSrv l s)) x
                    (coarsenBFs (upSrv l s′)) srowEq)
                  (LCI.cliSendRow (upLink l) hi (coarsenBFc (upClient l s)) x
                    (coarsenBFc (upClient l s′)) crowEq))
-- NEITHER moved while the cell filled: the two ownership certificates decide it
...   | inj₁ (seq , nsrv) | inj₁ (ceq , ncli) =
        ⊥-elim (fill-noPeer-⊥ (upLink l) hi x
                  (role-in (upLink l) hi N2N_BlockFetch x) nsrv ncli)

-- … and the io READ's, the same dispatch at the other direction: the cell goes
-- `draining` (which holds no block) and the client's row travels with the SOURCE
-- cell's own phase, which is what the region's block-read refutation consumes
upReadData : (l : TwoLegs) (s s′ : SysState)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (draining x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ full x
  → LIC.CliRowP (upLink l) hi (upClient l s) (upClient l s′) (output l₀ d₀ id₀) x
  → ((cellUp l s ≡ cellUp l s′) ⊎ (LLI.CellFullBlk (cellUp l s′) → ⊥))
    × ((coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
       ⊎ (LCI.CliReadAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))
          × (cellUp l s ≡ full x)))
upReadData l s s′ l₀ d₀ id₀ x sEq srcFull crow
  with setRead⁺ (phase (med s)) l₀ d₀ id₀ (draining x) (upLink l) hi N2N_BlockFetch
... | inj₁ (miss , same) =
      inj₁ (trans (cellUp-key l s)
              (trans same
                (trans (sym (cong (λ m → phase m (upLink l) hi N2N_BlockFetch) sEq))
                       (sym (cellUp-key l s′)))))
    , inj₁ (cong coarsenBFc
              (cliRowR-off (upLink l) hi (upClient l s) (upClient l s′)
                           l₀ d₀ id₀ x miss crow))
... | inj₂ (refl , refl , refl , tgt) with crow
...   | inj₁ (ceq , _) =
        inj₂ (λ hc → drNotBlk (subst LLI.CellFullBlk
                                (trans (cellUp-key l s′)
                                  (trans (cong (λ m → phase m (upLink l) hi N2N_BlockFetch) sEq)
                                         tgt)) hc))
      , inj₁ (cong coarsenBFc ceq)
  where drNotBlk : LLI.CellFullBlk (draining x) → ⊥
        drNotBlk ()
...   | inj₂ (refl , refl , crowEq) =
        inj₂ (λ hc → drNotBlk (subst LLI.CellFullBlk
                                (trans (cellUp-key l s′)
                                  (trans (cong (λ m → phase m (upLink l) hi N2N_BlockFetch) sEq)
                                         tgt)) hc))
      , inj₂ ( LCI.cliReadRow (upLink l) hi (coarsenBFc (upClient l s)) x
                 (coarsenBFc (upClient l s′)) crowEq
             , trans (cellUp-key l s) srcFull )
  where drNotBlk : LLI.CellFullBlk (draining x) → ⊥
        drNotBlk ()

-- the api arm's two carried premises, read off the join's FIRST factor: the token
-- (three projections deep, `LiveDrvCSD` §4's own route) and the exclusion
upSent-of : (l : TwoLegs) (s : SysState) → LegJointU l s
          → (LDBA.UpCp4 (relayOf l s) ⊎ BFcHasBlk (upClient l s))
          → ProdSent (prodOf l s)
upSent-of l s j (inj₁ g)    =
  LDBA.upCp4⇒sent l s g (proj₁ (proj₁ (proj₁ (proj₁ j))))
upSent-of l s j (inj₂ hold) =
  proj₁ (proj₂ (proj₂ (proj₁ (proj₁ (proj₁ j))))) hold

upNtt-of : (l : TwoLegs) (s : SysState) → LegJointU l s → LS.NoTwoTokens l s
upNtt-of l s j = LTE.noTwoOf (proj₂ (proj₂ (proj₁ j)))

-- (T11e) … and the TOKEN itself, at `upSent-of`'s own projection depth: §6h's api
-- class derives `InCp03` from it per state under the guard (review C-1), so this is
-- the whole of what the fold adds to the arm's inputs
pinv-of : (l : TwoLegs) (s : SysState) → LegJointU l s → PipeInv l s
pinv-of l s j = proj₁ (proj₁ (proj₁ (proj₁ j)))

------------------------------------------------------------------------
-- §5e  (C, cellCp3) *** THE WINDOW'S TWO HALVES, COMPOSED — `CellCp3` IS A THEOREM
-- OF THE CARRIED JOIN. ***
--
-- HALF ONE is `LiveChanInv`'s `cvBlk` then `cvStr`: an unread BLOCK in a hop's cell
-- puts that hop's own reader inside its streaming region (`CliStrA`), off `ChanUp` /
-- `ChanDn` alone — no server hypothesis, no premise.  HALF TWO is what slices A and B
-- landed: `LDBA.UpIdl` / `LBFD.DnIdl` say the reader sits at `bcIdle` throughout its
-- PRE-REQUEST region, and `LCI.CliStrA NS.bcIdle = ⊥`.  So the two contradict at every
-- position of the guard, and the conclusion is the one sub-phase the guard leaves:
-- `cp3`.
--
-- *** THE UNION IS WHAT MAKES THIS A COMPOSITION AND NOT A CASE ANALYSIS. ***  The
-- guard and the goal PARTITION the premise's own position hypothesis — `UpPre ∪
-- RelayCp3 = RelayPre` and `DnPre ∪ ConsCp3 = InCp03`, both inclusions AND
-- disjointness machine-checked on all seventeen / all seven shapes in slice B's
-- step-0 probe — so a REFUTATION of the guard IS the goal, which is the shape of the
-- two position lemmas below.
--
-- *** NEITHER `relayPre-cases` NOR `inCp03-cases` IS NEEDED *** (the gate's Q0 stated
-- both as Σ-enumerations): all four regions are TOTAL dispatches, so the lemmas
-- dispatch on the phase SHAPE directly and the union is read off the clause bodies. A
-- new sub-phase is therefore a coverage error here, in both directions.
------------------------------------------------------------------------

-- `cvStr`'s two arms at a cell that holds an unread block: the `MsgStartBatch` arm
-- dies on the cell's OWN `MsgBlock` payload, the quiet arm IS the client region
chanStr-blk : (b : Block₃) (ph : CopyPhase) (ca : NS.BFcPos)
            → LLI.CellFull⁺ b ph → LCI.ChanStr ph ca → LCI.CliStrA ca
chanStr-blk b ph ca refl (inj₁ ((_ , _ , _ , ()) , _))
chanStr-blk b ph ca refl (inj₂ (_ , hstr)) = hstr

-- HALF ONE, at ABSTRACT hop positions: an unread block in the cell ⇒ the hop's client
-- is in its streaming region (`cvBlk` reports the server, `cvStr` the channel)
blkFull⇒cliStr : (sa : NS.BFsPos) (b : Block₃) (ph : CopyPhase) (ca : NS.BFcPos)
               → LLI.CellFull⁺ b ph → LCI.ChanInv sa ph ca → LCI.CliStrA ca
blkFull⇒cliStr sa b ph ca hf iv =
  chanStr-blk b ph ca hf
    (LCI.ChanInv.cvStr iv (LCI.ChanInv.cvBlk iv (b , _ , _ , _ , hf)))

-- HALF TWO's position step at the UP hop: `UpPre` and `RelayCp3` partition
-- `RelayPre`, so refuting the guard leaves the conclusion
--
-- (F115  *** THE PARTITION'S OTHER HALF: THE GUARD DOES NOT CONTAIN THE CONCLUSION. ***)
--      F109/F112 guarded the region's CLOSURE (widening it to `cp3` breaks preservation);
--      this guards its DISJOINTNESS from the goal, which is what the composition spends.
--      Answer the `cp3` clause the way the other three are answered —
--      `upPre-cp3 (consuming _ cp3) n _ = ⊥-elim (n tt)`, i.e. claim the guard holds
--      there too.  *** RED ***: `LiveChanJoin.agda:2318.45-47: error: [UnequalTerms]
--      (Level.Lift _ℓ_3622 ⊤₀) !=< ⊥ when checking that the expression tt has type
--      LAC.UpPre (consuming x cp3)`, EXIT=42 — `UpPre` is `⊥` at exactly the sub-phase
--      the window concludes, so the guard cannot swallow the goal and the `cp3` clause
--      must ANSWER rather than refute.  Reverted by string inversion.
upPre-cp3 : (x : CPPh) → (LAC.UpPre x → ⊥) → RelayPre x → LLI.RelayCp3 x
upPre-cp3 (consuming _ cp0) n _ = ⊥-elim (n tt)
upPre-cp3 (consuming _ cp1) n _ = ⊥-elim (n tt)
upPre-cp3 (consuming _ cp2) n _ = ⊥-elim (n tt)
upPre-cp3 (consuming _ cp3) n _ = tt
upPre-cp3 (consuming _ cp4) n ()
upPre-cp3 (consuming _ cp5) n ()
upPre-cp3 (consuming _ cp6) n ()
upPre-cp3 (producing _ _)   n ()

-- … and at the DOWN hop, over the seven `ConsPh` shapes (`DnPre ∪ ConsCp3 = InCp03`)
dnPre-cp3 : (c : ConsPh) → (LBFD.DnPre c → ⊥) → InCp03 c → LLI.ConsCp3 c
dnPre-cp3 cp0 n _ = ⊥-elim (n tt)
dnPre-cp3 cp1 n _ = ⊥-elim (n tt)
dnPre-cp3 cp2 n _ = ⊥-elim (n tt)
dnPre-cp3 cp3 n _ = tt
dnPre-cp3 cp4 n ()
dnPre-cp3 cp5 n ()
dnPre-cp3 cp6 n ()

-- THE UP HALF (the gate's `upHalf`, landed): the carried channel invariant and slice
-- A's factor, and nothing else
--
-- (F114  *** THE THREE SLOTS OF `blkFull⇒cliStr` ARE ONE HOP's, AND WHICH HOP IS
--      MACHINE-CHECKED. ***)  the abstract half-one lemma takes a server, a cell and a
--      client separately, so a mis-routed hop is exactly the mistake `LiveLegAssembly`'s
--      own (M3) guards at the value layer.  Feed it the DOWN hop's server beside the UP
--      hop's cell and client (`coarsenBFs (dnSrv l s)` for `upSrv`).  *** RED ***:
--      `LiveChanJoin.agda:2344.48-51: error: [UnequalTerms] (upSrv l s) != (dnSrv l s)
--      of type BFsPos when checking that the expression ivU has type LCI.ChanInv
--      (coarsenBFs (dnSrv l s)) (cellUp l s) (coarsenBFc (upClient l s))`, EXIT=42 —
--      the carried `ChanUp` pins all three slots together, so the composition cannot
--      cross the two hops even accidentally.  Reverted by string inversion.
upCellCp3 : (l : TwoLegs) (s : SysState) (b : Block₃)
          → LCI.ChanUp l s → LDBA.UpIdl l s
          → LLI.CellFull⁺ b (cellUp l s) → RelayPre (relayOf l s)
          → LLI.RelayCp3 (relayOf l s)
upCellCp3 l s b ivU hidl hf =
  upPre-cp3 (relayOf l s)
    (λ g → subst LCI.CliStrA (hidl g)
             (blkFull⇒cliStr (coarsenBFs (upSrv l s)) b (cellUp l s)
                (coarsenBFc (upClient l s)) hf ivU))

-- … and THE DOWN HALF (the gate's `dnHalf`), off slice B's factor
dnCellCp3 : (l : TwoLegs) (s : SysState) (b : Block₃)
          → LCI.ChanDn l s → LBFD.DnIdl l s
          → LLI.CellFull⁺ b (cellDn l s) → InCp03 (phOf l s)
          → LLI.ConsCp3 (phOf l s)
dnCellCp3 l s b ivD hidl hf =
  dnPre-cp3 (phOf l s)
    (λ g → subst LCI.CliStrA (hidl g)
             (blkFull⇒cliStr (coarsenBFs (dnSrv l s)) b (cellDn l s)
                (coarsenBFc (dnClient l s)) hf ivD))

-- *** THE WINDOW, DISCHARGED: `LiveLegStep.CellCp3` OFF THE CARRIED JOIN ALONE. ***
-- The three factors it reads are `LegJointU`'s FOURTH (`ChanLeg`, both hops), FIFTH
-- (`BFJoint`'s third member) and EIGHTH (`UpJoint`'s third member).  Slice D makes
-- this the supplier of the assembly's LAST PREMISE — after which
-- `LivenessProof.Premises` is EMPTY and `livenessSpec` is UNCONDITIONAL.
cellCp3-of : (l : TwoLegs) (r : RState) (b : Block₃)
           → LegJointU l (toSys r) → LS.CellCp3 l b r
cellCp3-of l r b j =
    upCellCp3 l (toSys r) b (chanUp-of l (toSys r) j)
      (LDBA.upJoint⇒idl l (toSys r) (upJoint-of l (toSys r) j))
  , dnCellCp3 l (toSys r) b (chanDn-of l (toSys r) j)
      (LBFD.bfJoint⇒dnIdl l (toSys r) (bfJoint-of l (toSys r) j))

------------------------------------------------------------------------
-- §6  THE FIVE ARMS.  Each arm CALLS the assembly's own arm at the
-- SAME arguments — so the successor is literally the same term — and pairs its map
-- with the channel half proved above.  These five ARE the module's interface:
-- `LiveFSim` owns the label dispatch that selects between them (see the closing
-- note).
------------------------------------------------------------------------

-- *** (D, cellCp3) NO PREMISE PARAMETER ANY MORE. ***  This block used to open
-- `module _ (cellCp3 : (l) (b) (r) → LS.CellCp3 l b r) where` and pass that ∀-`RState`
-- assumption on to the assembly's five arms.  Four of the five never read it, and the
-- fifth (the io READ class) now takes it as the FIRST argument of its preservation
-- MAP — so `tauIoU-out` supplies it INSIDE its own `λ f`, where the join `f` is in
-- hand, off §5e's `cellCp3-of`.  That is the discharge: the fact is a THEOREM of the
-- carried invariant at the arm's own source state, and nothing above this module
-- carries a premise for it.
module _ where

  -- the medium-τ class at the joined invariant
  τpreserveU-med : (r : RState) {M M′ : NetProc}
      (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
      (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (LegJointUB legBD (toSys r) → LegJointUB legBD (toSys r′))
  τpreserveU-med r ms Meq =
    let (r′ , Meq′ , pres) = LA.τpreserveB-med r ms Meq
        (i , d₀ , id₀ , x , drainEq , _) = medium-τ-inv-wt (med (toSys r)) ms
    in  r′ , Meq′
      , λ f l → mkU l _ (pres (legJointB-of (toSys r) f) l)
                  (chanLeg-drain l (toSys r) i d₀ id₀ x drainEq
                     (chanLeg-of l (toSys r) (f l)))
                  -- (T11h) the fifth factor's two halves, at one `mkBFJoint`
                  -- (B, cellCp3) … and its THIRD, a frame off the same slot tuple
                  (LBFD.mkBFJoint l (toSys r) _
                     (drvBF-drain l (toSys r) i d₀ id₀)
                     (bfFreshU-drain l (toSys r) i d₀ id₀ x drainEq)
                     (dnIdlU-drain l (toSys r) i d₀ id₀)
                     (bfJoint-of l (toSys r) (f l)))
                  -- (T6c) the CS half: the drained key hits at most one of the two CS
                  -- cells and all four CS peers are fixed (`drainSucc` keeps the four
                  -- node records LITERAL), so this arm needs no cone at all
                  (LCJC.chanCSLeg-drain l (toSys r) i d₀ id₀ x drainEq
                     (chanCSLeg-of l (toSys r) (f l)))
                  -- (T8c-iii) node D's pair: the drained key is this leg's own dn CS
                  -- cell or it is not, and either way the four node slots are `refl`
                  (dnJointU-drain l (toSys r) i d₀ id₀ x drainEq
                     (dnJoint-of l (toSys r) (f l)))
                  -- (T10) the up hop's pair: `drain-nodes` reports node A's slots and
                  -- the relay's, and the drained key leaves the up cell either fixed
                  -- or EMPTY — which holds no block
                  (LDBA.upJoint-drainish l (toSys r) _
                     (proj₁ (LS.drain-nodes l (toSys r) i d₀ id₀))
                     (proj₁ (proj₂ (LS.drain-nodes l (toSys r) i d₀ id₀)))
                     (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
                        (LS.drain-nodes l (toSys r) i d₀ id₀))))))))
                     (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
                        (LS.drain-nodes l (toSys r) i d₀ id₀))))))
                     (upCellDrain l (toSys r) i d₀ id₀)
                     (upJoint-of l (toSys r) (f l)))

  -- the `break` class
  evStepU-break : (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
    → radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (LegJointUB legBD (toSys r) → LegJointUB legBD (toSys r′))
  evStepU-break r l₀ {a} step =
    let (r′ , Mr , pres) = LA.evStepB-break r l₀ step
    in  r′ , Mr
      , λ f l → mkU l _ (pres (legJointB-of (toSys r) f) l)
                  (chanLeg-break l r l₀ step (chanLeg-of l (toSys r) (f l)))
                  (LBFD.mkBFJoint l (toSys r) _
                     (drvBF-break l r l₀ step)
                     (bfFreshU-break-at l r l₀ step)
                     (dnIdlU-break-at l r l₀ step)
                     (bfJoint-of l (toSys r) (f l)))
                  -- (T6c) … and the CS half, likewise cone-free
                  (chanCSLeg-break l r l₀ step (chanCSLeg-of l (toSys r) (f l)))
                  -- (T8c-iii) … and node D's pair, framed
                  (dnJointU-break-at l r l₀ step (dnJoint-of l (toSys r) (f l)))
                  -- (T10) a `break` moves only the medium's FLAG, so every node slot
                  -- is a literal and the cell's phase function is fixed
                  (LDBA.upJoint-frame l (toSys r) _
                     (proj₁ (upMed-fix l (toSys r) (proj₁ (break-invert r l₀ {a} step))))
                     (proj₁ (proj₂ (upMed-fix l (toSys r) (proj₁ (break-invert r l₀ {a} step)))))
                     (proj₁ (proj₂ (proj₂ (upMed-fix l (toSys r) (proj₁ (break-invert r l₀ {a} step))))))
                     (proj₂ (proj₂ (proj₂ (upMed-fix l (toSys r) (proj₁ (break-invert r l₀ {a} step))))))
                     (trans (cellUp-key l (toSys r))
                        (trans (sym (cong (λ g → g (upLink l) hi N2N_BlockFetch)
                                      (proj₁ (proj₂ (proj₂ (break-invert r l₀ {a} step))))))
                               (sym (cellUp-key l _))))
                     (upJoint-of l (toSys r) (f l)))

  -- the visible api class (grant #8's rows for the up hop, §8's node-D re-mirror
  -- for the down hop, both off the cone's four row FIELDS)
  evStepU-api : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
    → IsApiCSBF e → apiES .mem (X , e) a
    → radec r ─[ ev (evl (evLabel X e a)) ]─► M
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (LegJointUB legBD (toSys r) → LegJointUB legBD (toSys r′))
  evStepU-api r {X} {e} {a} aic apimem step =
    let (r′ , Mr , pres) = LA.evStepB-api r aic apimem step
        (N₁ , ns , _) = LA.api-nodes-solo r aic step
        -- (T3b) the cone's report is a RECORD: the four row slots and (T1's) two
        -- driver pairs are read BY NAME, so an inserted slot can no longer shift them
        de       = driverExpose⁺ (toSys r) apimem ns
        s′       = deSucc de
        medEq    = deMed de
        rowsBD   = deRowsAB de
        rowsCD   = deRowsAC de
        dnRowsBD = deRowsBD de
        dnRowsCD = deRowsCD de
        dnDrvBD  = deDnDrvBD de
        dnDrvCD  = deDnDrvCD de
        -- (T5) … and the two legs' CS-server pairs, read BY NAME beside them
        csDrvBD  = deCsDrvBD de
        csDrvCD  = deCsDrvCD de
        -- (T7) … and the two legs' UP-hop CS-CLIENT chains, read BY NAME beside them
        upCsDrvBD = deUpCsDrvBD de
        upCsDrvCD = deUpCsDrvCD de
        -- (T6c, grant #12) … and the CS channel invariant's four api slots: the
        -- relays' pairs (up CLIENT, down SERVER) beside node A's up-hop SERVERS and
        -- node D's down-hop CLIENTS, all read BY NAME
        csRowsBD = deCSRowsBD de
        csRowsCD = deCSRowsCD de
        csUpSrvBD = deCSUpSrvBD de
        csUpSrvCD = deCSUpSrvCD de
        csDnCliBD = deCSDnCliBD de
        csDnCliCD = deCSDnCliCD de
    in  r′ , Mr
      -- (T11e) the CS-channel SUCCESSOR is BOUND, not called twice: §6h's keystone
      -- reads `ccQui`/`ccPre` off its DOWN hop, and a second occurrence would
      -- re-elaborate the whole argument tuple (M-5's rule, second application)
      , λ f l → let -- (T11h) node D's WIDE field, BOUND: §6h's carry and the BF
                     -- freshness clause both read it, at the same type
                     ndF  = nodeDF l (deNodeDBD de) (deNodeDCD de)
                     -- (B, cellCp3) … and the NARROWING of it, bound for M-5's reason:
                     -- the freshness half and the new third member read the same value
                     ndBF = bfNodeD-of l (toSys r) s′ ndF
                              (proj₂ (rowsDn l dnRowsBD dnRowsCD))
                     csl′ = LCJC.chanCSLeg-api l (toSys r) s′ e a medEq
                             (csApiUp l (toSys r) s′ e a csUpSrvBD csUpSrvCD csRowsBD csRowsCD)
                             (csApiDn l (toSys r) s′ e a csDnCliBD csDnCliCD csRowsBD csRowsCD)
                             (chanCSLeg-of l (toSys r) (f l))
                in
                mkU l _ (pres (legJointB-of (toSys r) f) l)
                  (chanLeg-api l (toSys r) s′ e a medEq
                     (rowsUp l rowsBD rowsCD) (rowsDn l dnRowsBD dnRowsCD)
                     (chanLeg-of l (toSys r) (f l)))
                  -- *** (T11h) THE FIFTH FACTOR's TWO HALVES AT THE api CLASS. ***  The
                  -- coupling reads the cone's `DnSrvDrv` (its two landings) and the
                  -- freshness clause reads the SAME field for its new third member,
                  -- beside the relay's advance and node D's narrowed pair
                  (LBFD.mkBFJoint l (toSys r) s′
                     (LDB.drvBF-api l (toSys r) s′ (drvDn l dnDrvBD dnDrvCD)
                        (csDrv l csDrvBD csDrvCD)
                        -- (T7) … and the `cp5` chain's own cone pair, selected the same way
                        (upCsDrv l upCsDrvBD upCsDrvCD))
                     (bfFreshU-api l (toSys r) s′ medEq (drvDn l dnDrvBD dnDrvCD)
                        (relayA l (deRelayAdvBD de) (deRelayAdvCD de))
                        ndBF)
                     -- (B, cellCp3) … and the third member's WHOLE api arm: node D's
                     -- own joint adjacency, and the datatype's phase indices close it
                     (LBFD.dnIdl-api l (toSys r) s′ ndBF)
                     (bfJoint-of l (toSys r) (f l)))
                  -- (T6c) the CS half at the visible class
                  csl′
                  -- *** (T8c-iii) node D's pair at the api class — the four-way
                  -- dispatch of §5f, fed by the two MERGED cone fields. ***
                  (dnJointU-api l (toSys r) s′ medEq
                     (relayF l (deRelayBD de) (deRelayCD de))
                     (relayA l (deRelayAdvBD de) (deRelayAdvCD de))
                     ndF
                     (proj₁ (csApiDn l (toSys r) s′ e a csDnCliBD csDnCliCD csRowsBD csRowsCD))
                     (proj₂ (csApiDn l (toSys r) s′ e a csDnCliBD csDnCliCD csRowsBD csRowsCD))
                     -- (T11e) §6h's three: the cone's `DnCsDrv` at the ACCESSOR form
                     -- (a second `_`-typed leg selector, `csDrv`'s reason exactly), the
                     -- carried token, and the hop's channel invariant at the successor
                     (csDrvO l csDrvBD csDrvCD)
                     (pinv-of l (toSys r) (f l))
                     (proj₂ csl′)
                     (dnJoint-of l (toSys r) (f l)))
                  -- *** (T10) the up hop's pair at the api class: the cell is fixed
                  -- (an api leaves the medium alone), the driver step and the leaf
                  -- record carry node A's half, and the (T10) `UpBfDrv` slot carries
                  -- the relay's.  The two carried premises are the token's `ProdSent`
                  -- at the guard and the exclusion at the client's hold ***
                  (LDBA.upJoint-api l (toSys r) s′ {_} {e} {a}
                     (trans (cellUp-key l (toSys r))
                        (trans (cong (λ m → phase m (upLink l) hi N2N_BlockFetch) medEq)
                               (sym (cellUp-key l s′))))
                     (ldSel l (deLdBD de) (deLdCD de))
                     (vlSel l (deVlBD de) (deVlCD de))
                     (ubfSel l (deUpBfBD de) (deUpBfCD de))
                     (upSent-of l (toSys r) (f l))
                     (upNtt-of l (toSys r) (f l))
                     (upJoint-of l (toSys r) (f l)))
    where
    -- the cone reports per LEG; these pick the leg's own pair (one selector per hop,
    -- because the two hops' pair types differ)
    rowsUp : (l : TwoLegs) → _ → _ → _
    rowsUp legBD bd cd = bd
    rowsUp legCD bd cd = cd
    rowsDn : (l : TwoLegs) → _ → _ → _
    rowsDn legBD bd cd = bd
    rowsDn legCD bd cd = cd
    -- (T1) … and the same selector for S1's own slot
    drvDn : (l : TwoLegs) → _ → _ → _
    drvDn legBD bd cd = bd
    drvDn legCD bd cd = cd
    -- (T5) … and for the CS one.  The leg has to be a CONSTRUCTOR for the cone's
    -- node-field form and the coupling's `dnCSs`/`relayOf` form to be convertible,
    -- which is exactly what this dispatch supplies
    -- (`_`-typed against the read-the-type discipline, deliberately and for `drvDn`'s
    -- reason: the two sides are the cone's node-PROJECTION form and the coupling's
    -- `dnCSs`/`relayOf` form, and spelling either out here would fix the one the leg
    -- dispatch exists to convert between — review M-5)
    csDrv : (l : TwoLegs) → _ → _ → _
    csDrv legBD bd cd = bd
    csDrv legCD bd cd = cd
    -- (T11e) … and the SAME cone field at the OTHER accessor form.  `csDrv` is
    -- `_`-typed so each use infers its own type, and `LDB.drvBF-api` reads the
    -- coupling's `dnCSs` form while §6h's record reads `LiveChanCS.dnCSsOf`: two uses
    -- at two types need two selectors, and the leg CONSTRUCTOR is what makes each
    -- convertible (the banked `dnCSs`/`dnCSsOf` bridge, avoided rather than crossed)
    csDrvO : (l : TwoLegs) → _ → _ → _
    csDrvO legBD bd cd = bd
    csDrvO legCD bd cd = cd
    -- (T7) … and for the `cp5` chain's, `csDrv`'s reason exactly (the two sides are the
    -- cone's node-PROJECTION form and the coupling's `upCSc`/`relayOf` form)
    upCsDrv : (l : TwoLegs) → _ → _ → _
    upCsDrv legBD bd cd = bd
    upCsDrv legCD bd cd = cd
    -- (T8c-iii) … and the three the api carry reads, `csDrv`'s reason exactly (the two
    -- sides are the cone's node-PROJECTION form and the carry's accessor form)
    relayF : (l : TwoLegs) → _ → _ → _
    relayF legBD bd cd = bd
    relayF legCD bd cd = cd
    relayA : (l : TwoLegs) → _ → _ → _
    relayA legBD bd cd = bd
    relayA legCD bd cd = cd
    nodeDF : (l : TwoLegs) → _ → _ → _
    nodeDF legBD bd cd = bd
    nodeDF legCD bd cd = cd
    -- (T10) … and the three the up hop's pair reads, `csDrv`'s reason exactly
    ldSel : (l : TwoLegs) → _ → _ → _
    ldSel legBD bd cd = bd
    ldSel legCD bd cd = cd
    vlSel : (l : TwoLegs) → _ → _ → _
    vlSel legBD bd cd = bd
    vlSel legCD bd cd = cd
    ubfSel : (l : TwoLegs) → _ → _ → _
    ubfSel legBD bd cd = bd
    ubfSel legCD bd cd = cd

  -- the io FILL class (grant #7's rows, all four peers)
  tauIoU-in : (r : RState)
      (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
    → ioES .mem (Payload , input l₀ d₀ id₀) x
    → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► M₁
    → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► N₁
    → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (LegJointUB legBD (toSys r) → LegJointUB legBD (toSys r′))
  tauIoU-in r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
    let (r′ , Mr , pres) = LA.tauIoB-in r l₀ d₀ id₀ x iomem sM sN Meq
        (srcEmpty , _) = medium-ev-in-key (med (toSys r)) l₀ d₀ id₀ x sM
        cone = top-nodes-io-evoP⁺ (toSys r) {Payload} {input l₀ d₀ id₀} {x} {N₁} iomem sN
        s″ : SysState
        s″ = proj₁ cone
        -- (T1) the cone's NINTH and TENTH slots are the two relay nodes' driver
        -- phases, which is S1's io premise; (T5, grant #11) the LAST slot is the two
        -- tracked CS SERVERS' io facts, which is the `pp1` arm's
        -- (T6c, grant #12) the cone grew two TRAILING components (the up-hop CS
        -- servers and the four CS clients), and this reader ended on a NON-wildcard,
        -- so it is re-cut with two `_`s — the banked Σ-append trap, third sighting
        -- (T8c-iii) positions ELEVEN and TWELVE are node D's two driver slots, fixed
        -- across an io step, and they are what the coupling's io classes need.  They
        -- were already in the cone (`LiveLegIoCone:1092`, `:1159`) — bound here rather
        -- than re-derived
        -- (T10) positions SEVEN and EIGHT are node A's two producer slots, fixed
        -- across an io step — the eighth factor's own frame reads them
        (_ , _ , _ , _ , cliP , srvP , prodAB , prodAC , cpB , cpC , cnsBD , cnsCD , _ , cssP
          , cssUpP , cscP) = cone
        s′ : SysState
        s′ = mkSys (mkMed (phase-upd (phase (med (toSys r))) l₀
                            (setCell (phase (med (toSys r)) l₀) d₀ id₀ (full x)))
                          (broken (med (toSys r))))
                   (nA s″) (nB s″) (nC s″) (nD s″)
    in  r′ , Mr
      -- (T11, M-5) the up hop's fill datum is BOUND, not called twice.  Both of its
      -- components are wanted by `upJoint-fill` at IDENTICAL arguments, and a second
      -- occurrence re-elaborates the whole argument tuple (four `*Row` applications
      -- and the medium equation) for nothing.  The binding has to sit INSIDE the `λ`
      -- because every argument mentions the lambda-bound leg `l`
      , λ f l → let ufd = upFillData l (toSys r) s′ l₀ d₀ id₀ x refl srcEmpty
                            (upSrvRow l (toSys r) s′ (input l₀ d₀ id₀) x srvP)
                            (upCliRow l (toSys r) s′ (input l₀ d₀ id₀) x cliP)
                in
                mkU l _ (pres (legJointB-of (toSys r) f) l)
                  (chanLeg-fill l (toSys r) s′ l₀ d₀ id₀ x refl srcEmpty srvP cliP
                     (chanLeg-of l (toSys r) (f l)))
                  (LBFD.mkBFJoint l (toSys r) s′
                     (LDB.drvBF-fill l (toSys r) s′ l₀ d₀ id₀ x
                        (LDB.relayFix-of l (toSys r) s′ cpB cpC)
                        (dnSrvRow l (toSys r) s′ (input l₀ d₀ id₀) x srvP)
                        (dnCssRow l (toSys r) s′ (input l₀ d₀ id₀) x cssP)
                        -- (T7) … and the up-hop CLIENT's io fact, the `cp5` chain's own
                        (upCscRow l (toSys r) s′ (input l₀ d₀ id₀) x cscP))
                     -- (T11h) the freshness half rides the SAME two dn-hop io rows the
                     -- channel invariant's own arm takes
                     (bfFreshU-fill l (toSys r) s′ l₀ d₀ id₀ x refl srcEmpty
                        (LDB.relayFix-of l (toSys r) s′ cpB cpC)
                        (phFix l cnsBD cnsCD)
                        (dnSrvRow l (toSys r) s′ (input l₀ d₀ id₀) x srvP)
                        (dnCliRow l (toSys r) s′ (input l₀ d₀ id₀) x cliP))
                     -- (B, cellCp3) … and the third member, off the SAME client row
                     (dnIdlU-fill l (toSys r) s′ l₀ d₀ id₀ x (phFix l cnsBD cnsCD)
                        (dnCliRow l (toSys r) s′ (input l₀ d₀ id₀) x cliP))
                     (bfJoint-of l (toSys r) (f l)))
                  -- (T6c, grant #12) the CS half at the io FILL class — the arm the
                  -- whole grant exists for.  Its *(neither peer moved)* case is
                  -- discharged INSIDE `LiveChanJoinCS`, from the ownership
                  -- certificates the granted cone's fixity arms carry.
                  (LCJC.chanCSLeg-fill l (toSys r) s′ l₀ d₀ id₀ x refl srcEmpty
                     (csIoUp l (toSys r) s′ (input l₀ d₀ id₀) x cssUpP cscP)
                     (csIoDn l (toSys r) s′ (input l₀ d₀ id₀) x cssP cscP)
                     (chanCSLeg-of l (toSys r) (f l)))
                  -- (T8c-iii) node D's pair at the io FILL class: the CLIENT's own
                  -- request write is the step that ESTABLISHES the freshness clause's
                  -- correlation, and the server's five writes are refuted by its region
                  (dnJointU-fill l (toSys r) s′ l₀ d₀ id₀ x refl srcEmpty
                     (LDB.relayFix-of l (toSys r) s′ cpB cpC)
                     (phFix l cnsBD cnsCD)
                     (proj₁ (csIoDn l (toSys r) s′ (input l₀ d₀ id₀) x cssP cscP))
                     (proj₂ (csIoDn l (toSys r) s′ (input l₀ d₀ id₀) x cssP cscP))
                     (dnJoint-of l (toSys r) (f l)))
                  -- (T10) the up hop's pair at the io FILL class: node A's driver is
                  -- fixed across an io step (the cone's positions 7-8) and §5i's
                  -- builder pairs the fill with the row that caused it
                  (LDBA.upJoint-fill l (toSys r) s′ l₀ d₀ id₀ x
                     (prodFix-of l (toSys r) s′ prodAB prodAC)
                     (LDB.relayFix-of l (toSys r) s′ cpB cpC)
                     (upSrvRow l (toSys r) s′ (input l₀ d₀ id₀) x srvP)
                     (proj₁ ufd) (proj₂ ufd)
                     (upJoint-of l (toSys r) (f l)))

  -- the io READ class
  tauIoU-out : (r : RState)
      (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
    → ioES .mem (Payload , output l₀ d₀ id₀) x
    → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► M₁
    → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► N₁
    → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (LegJointUB legBD (toSys r) → LegJointUB legBD (toSys r′))
  tauIoU-out r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
    let (r′ , Mr , pres) = LA.tauIoB-out r l₀ d₀ id₀ x iomem sM sN Meq
        (srcFull , _) = medium-ev-out-key (med (toSys r)) l₀ d₀ id₀ x sM
        cone = top-nodes-io-evoP⁺ (toSys r) {Payload} {output l₀ d₀ id₀} {x} {N₁} iomem sN
        s″ : SysState
        s″ = proj₁ cone
        -- (T1) the same two driver-phase slots, at the READ label, and (T5) the same
        -- CS pair behind them
        -- (T6c, grant #12) the cone grew two TRAILING components (the up-hop CS
        -- servers and the four CS clients), and this reader ended on a NON-wildcard,
        -- so it is re-cut with two `_`s — the banked Σ-append trap, third sighting
        -- (T8c-iii) positions ELEVEN and TWELVE are node D's two driver slots, fixed
        -- across an io step, and they are what the coupling's io classes need.  They
        -- were already in the cone (`LiveLegIoCone:1092`, `:1159`) — bound here rather
        -- than re-derived
        -- (T10) positions SEVEN and EIGHT are node A's two producer slots, fixed
        -- across an io step — the eighth factor's own frame reads them
        (_ , _ , _ , _ , cliP , srvP , prodAB , prodAC , cpB , cpC , cnsBD , cnsCD , _ , cssP
          , cssUpP , cscP) = cone
        s′ : SysState
        s′ = mkSys (mkMed (phase-upd (phase (med (toSys r))) l₀
                            (setCell (phase (med (toSys r)) l₀) d₀ id₀ (draining x)))
                          (broken (med (toSys r))))
                   (nA s″) (nB s″) (nC s″) (nD s″)
    in  r′ , Mr
      -- (T11, M-5) … and the READ direction's datum, bound for the same reason
      , λ f l → let urd = upReadData l (toSys r) s′ l₀ d₀ id₀ x refl srcFull
                            (upCliRow l (toSys r) s′ (output l₀ d₀ id₀) x cliP)
                in
                -- (D, cellCp3) *** THE DISCHARGE, AT ITS ONE SITE. ***  The read
                -- class's map takes the window fact per leg; §5e proves it off this
                -- very `f`, so the premise never leaves this line
                mkU l _ (pres (λ lc b → cellCp3-of lc r b (f lc))
                              (legJointB-of (toSys r) f) l)
                  (chanLeg-read l (toSys r) s′ l₀ d₀ id₀ x refl srcFull srvP cliP
                     (chanLeg-of l (toSys r) (f l)))
                  (LBFD.mkBFJoint l (toSys r) s′
                     (LDB.drvBF-read l (toSys r) s′ l₀ d₀ id₀ x
                        (LDB.relayFix-of l (toSys r) s′ cpB cpC)
                        (dnSrvRow l (toSys r) s′ (output l₀ d₀ id₀) x srvP)
                        (dnCssRow l (toSys r) s′ (output l₀ d₀ id₀) x cssP)
                        -- (T7) … and the READ direction's twin
                        (upCscRow l (toSys r) s′ (output l₀ d₀ id₀) x cscP))
                     (bfFreshU-read l (toSys r) s′ l₀ d₀ id₀ x refl srcFull
                        (LDB.relayFix-of l (toSys r) s′ cpB cpC)
                        (phFix l cnsBD cnsCD)
                        (dnSrvRow l (toSys r) s′ (output l₀ d₀ id₀) x srvP)
                        (dnCliRow l (toSys r) s′ (output l₀ d₀ id₀) x cliP))
                     -- (B, cellCp3) … and the third member, off the SAME client row
                     (dnIdlU-read l (toSys r) s′ l₀ d₀ id₀ x (phFix l cnsBD cnsCD)
                        (dnCliRow l (toSys r) s′ (output l₀ d₀ id₀) x cliP))
                     (bfJoint-of l (toSys r) (f l)))
                  -- (T6c) … and at the io READ class
                  (LCJC.chanCSLeg-read l (toSys r) s′ l₀ d₀ id₀ x refl srcFull
                     (csIoUp l (toSys r) s′ (output l₀ d₀ id₀) x cssUpP cscP)
                     (csIoDn l (toSys r) s′ (output l₀ d₀ id₀) x cssP cscP)
                     (chanCSLeg-of l (toSys r) (f l)))
                  -- (T8c-iii) node D's pair at the io READ class: the SERVER's own
                  -- read is the step the `cp6`/`pp0` arms' equation names
                  (dnJointU-read l (toSys r) s′ l₀ d₀ id₀ x refl srcFull
                     (LDB.relayFix-of l (toSys r) s′ cpB cpC)
                     (phFix l cnsBD cnsCD)
                     (proj₁ (csIoDn l (toSys r) s′ (output l₀ d₀ id₀) x cssP cscP))
                     (proj₂ (csIoDn l (toSys r) s′ (output l₀ d₀ id₀) x cssP cscP))
                     (dnJoint-of l (toSys r) (f l)))
                  -- (T10) … and at the io READ class, off §5i's read builder
                  (LDBA.upJoint-read l (toSys r) s′ l₀ d₀ id₀ x
                     (prodFix-of l (toSys r) s′ prodAB prodAC)
                     (LDB.relayFix-of l (toSys r) s′ cpB cpC)
                     (upSrvRow l (toSys r) s′ (output l₀ d₀ id₀) x srvP)
                     (proj₁ urd) (proj₂ urd)
                     (upJoint-of l (toSys r) (f l)))

  -- *** THE TWO LABEL-DISPATCH TABLES ARE DELIBERATELY NOT COPIED HERE. ***  A
  -- `tauIoU` / `tauStepU` / `evStepU` / `legJointU-step` quartet was written and then
  -- DELETED (task-4b review, I-4).  `LiveFSim` re-does both dispatches itself —
  -- `fwdT-io` (`LiveFSim:1502`), `fwdT-τ` (`:1531`), `fwdT-vis` (`:1568`), each already
  -- carrying its own keep-in-sync note against `LiveLegAssembly` — because its arms owe
  -- extra cone facts and a `specPos` equation a generic fold cannot carry; so it
  -- consumes only the five per-class arms ABOVE, and the quartet had ZERO consumers.  A
  -- third copy of the assembly's two tables is pure sync surface: do not re-add it —
  -- add the missing class to `LiveFSim`'s tables instead.

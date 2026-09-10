{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cross-node api campaign, Tasks 8a/8b — NODE D's ChainSync machinery for the
-- `cp6`/`pp0` arms (`LiveRelayCS` §1's TWO surviving clauses, item (iv) of that
-- file's §6 classification).
--
-- WHY THIS FILE EXISTS.  The arms say "at a STABLE state whose relay driver is at
-- `consuming _ cp6` / `producing _ pp0`, the leg's down-hop CS SERVER is at
-- `csAreq`", and `csAreq` is reached ONLY by that server READING node D's
-- `MsgCSRequestNext` off the down CS cell (`NodeSpecs.csSnxt:416-418`).  The T8
-- gate (recorded at `LiveRelayCS` §6(iv)) settled which of the thirteen server
-- positions the stability argument has to close and which the invariant must
-- exclude: *** exactly ONE position is refutable-and-not-yet-refuted, `csIdle`,
-- and its `(empty cell , client at ccIdle)` sub-case is an api SYNC INSIDE NODE
-- D. ***  That sub-case is what §2 below refutes.
--
-- WHAT IS HERE, AND WHAT IS NOT.
--   §1  node D's CS driver-tail coupling — the predicate and its two funded
--       clauses (`cp0` ↔ `ccIdle`, `cp1` ↔ the post region), with the total
--       dispatch and Π-bridge shape `LiveDrvBF.DrvBF`/`drvCp-of` established.
--   §2  THE api-SYNC INTRO KIT AT NODE D — the generic four-node lift
--       (`nodes-offer-D`, the missing event-generic sibling of
--       `LiveStableOffer.nodes-offer-B`/`-C`), the two per-leg sync kits, the
--       `cp0` driver offer, the `ccIdle` peer offer, and the refutation the
--       `csIdle` sub-case consumes.
--   §3  the two offers that sub-case needs (the `cp0` driver offer and the `ccIdle`
--       peer offer) and the leg-dispatched refutation `cliIdle-cp0-⊥`.
--   §4  THE FRESHNESS CLAUSE — the gate's inventory as Agda: the narrowed cell
--       arm (`ReqOnly`), the RELAY-PHASE GUARD (`RelayFresh`), the core record
--       `DnFreshC` on four abstract positions, the guarded carried form `DnFresh`,
--       and the sharpening `dnFresh⇒areq` that turns it plus `isStable` into the
--       arms' own equation.
--   §5  (T8b) *** THE PRESERVATION CALCULUS *** — six step classes on the core, the
--       guard's BACKWARD closure (`dnFresh-lift`), the state-level wrappers, and
--       node D's coupling preserved (§5c: the api class and the two io classes; its
--       base and frame were already in §1).
--   §6  (T8b) *** THE UNOFFERED-LABEL FAMILY *** — the first label-level driver
--       refusal in the tree, and the completeness argument for §5's `CliDrvAdj`.
--   §6c (T8c-ii) *** THE JOINT ADJACENCY'S PRODUCER *** — `cliDrvAdj-of`, total on the
--       driver's six hops, off the driver's own step plus `LiveLegApiCone` §2b⁵'s
--       bundle SHARPENING and §4b's three client edge pins.  This is what makes
--       `CliDrvAdj` (and hence §5's node-D api class and §5c's coupling carry) usable
--       rather than merely stated.
--   NOT here: the relay `DrvCp` exclusion clauses, the three `⊥`-premises of
--       `dnFresh⇒areq`, the join/cone carry and the discharge — and NOTHING
--       in this file is joined to the FSim's `Rel` yet (it is a LEAF: no existing
--       module imports it).
--
-- THE DIRECTION MATTERS, and it is why the kit had to be built rather than
-- reused.  Node D's api machinery in the tree is all INVERSION — "node D took an
-- api step, therefore ‥" (`LiveLegApiExpose:319-428`, `NodeDApiEvo`).  What a
-- stability refutation needs is the INTRO direction — "these two components both
-- offer this event, therefore the state is not stable" — and of that there is
-- exactly one instance, `LiveStableOffer.nodeD-offer-BD`/`-CD` at `cp3`, hard-wired
-- to `apiBF … recvBFBlock` and to a KEPT event (it feeds `whole-offer-BD`, whose
-- last step is `¬hidden-BD`).  §2 is that instance made EVENT-GENERIC and pointed
-- at the HIDDEN side of the hide arithmetic instead.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `funext`, and no
-- `with` in anything whose type mentions an imported `blkA`-parameterised
-- predicate — every dispatch is on an EXPLICIT argument (the campaign's
-- `blkA`-module rule).
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
-- the NON-polymorphic `⊤`, qualified: the carrier of the payload-free api tags
import Data.Unit as U
open import Data.Bool using ( false )
open import Data.Maybe using ( just; nothing )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; subst; trans; cong )
-- (T8c-ii) §6c's six label inversions `with` on `Net_Api-≟`, so the DECISION's two
-- constructors have to be named (§6's `rewrite ≟-yes-refl` needed neither).  Imported
-- QUALIFIED and not `open`ed: `no` is already a VARIABLE name in this file's refutation
-- premises (`srvFresh⇒areq`, §6b's three `-off` members), and an unqualified import
-- turns each of those binders into a pattern-synonym application
import Relation.Nullary as RN
-- the `Fin numLinks` decidable-equality instance `≟-yes-refl` needs in scope at a
-- VARIABLE link (`LiveRelayOpen`'s §3 imports it for the same reason)
open import Class.DecEq.Instances using ( DecEq-Fin )

open import Process_Trees using ( PTree; ExtI; isStable )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvCSD
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  -- `produce` is the relay driver's second leg: §5d's extractor crosses the `>>=`
  -- with it, exactly as `PipeEvRelay.cpStepKind-of` does
  using ( p; apiES; linkBD; linkCD; produce )
-- the two api TAGS §6's family refutes, and `ApiCSCar` so their carried types are
-- named by the tag rather than spelled out
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; apiCS; ApiCSCar
        ; sendCSRequestNext; sendCSFindIntersect; sendCSDone
        -- the four CS CLIENT labels §6's fix-round members refute or pin: the one
        -- chain label that moves the client on a READ, and the three that are absent
        -- from `consume` altogether
        ; recvCSRollforward; recvCSRollback
        ; recvCSIntersectFound; recvCSIntersectNotFound
        -- (T8c-ii) the THREE BlockFetch heads of `consume`'s `cp2 … cp4` tail: §6c's
        -- joint-adjacency producer inverts each one to learn that the fired label is
        -- an `apiBF`, at which the CS client's api fact IS its fixity.  The carriers
        -- are named by `ApiBFCar` rather than spelled out, so no `Data` name is added
        ; apiBF; ApiBFCar
        ; sendBFRequestRange; recvBFBlock; sendBFClientDone
        -- (T8c-iii) §9's `cssRowP-noLink` is total on `Net_Api`, so every constructor
        -- is named: seven of them have no `ApiHasLink` witness at all and their
        -- clauses are absurd
        ; done; input; output; apiKA; apiTS; apiLN; apiLF
        ; sndmsg; rcvmsg; tx; sndack; rcvack; ack; break ; store; env )
-- `MsgCSRequestNext` is the ONE message §4's narrowed cell arm admits (the T8
-- review's I-1); the wire tuple's other three components stay lenient, which is why
-- §5's cell refutation is stated over `MessageChainSync` and not over `Payload`
open import CSP.Examples.Cardano_network.Data p
  -- (T11) §6e's `cp2` api sync is at an OUTPUT prefix, so it names the RANGE the
  -- driver pins and needs its `DecEq` instance to unstick the value test
  using ( Payload; MessageChainSync; chainSync; MsgCSRequestNext; Header; Tip
        ; ChainRange; chainRange; Point; point; DecEq-ChainRange
        -- (T11) §6g's cell region names the two RESPONDER messages the `pp3` arm's
        -- own hop can have in flight
        ; MsgCSAwaitReply; MsgCSRollForward )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi; Mode
  -- (T8c-iii) §9's `cssRowP-noLink` dispatches on the `ApiHasLink` witness, whose
  -- `done` constructor is `IDs`-indexed
  ; IDs; N2N_ChainSync; N2N_BlockFetch; N2N_KeepAlive; N2N_TxSubmission
  ; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Time; Length )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
import CSP.Examples.Cardano_network.ChainSync p as CS
-- (T11) §6e's peer step is a BlockFetch api event, so the bundle rung needs the
-- BF alphabet's own `apiBFev`
import CSP.Examples.Cardano_network.BlockFetch p as BF

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( Skip; _∖_; _⦀_; viewV; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( ev; evl; evLabel; _─[_]─►_; sVis )
-- the `nothing ≡ just` clash §6's bridge closes on, and the two step-transport
-- lemmas §5d's extractor crosses the relay driver's `>>=` with
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( nothing-absurd; bind-ev-inv; step-fcong )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial; nA; nB; nC; nD )
-- the hop's cell phase lives in the medium: §4's cell conjunct dispatches on it
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA as SM
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              ; ConsDPh; consD; cph; cblk; decCons; decConsD
              -- the RELAY driver's phase type: §4's clause is GUARDED on it (the
              -- T8 review's I-2 — the object is false without the guard)
              ; CPPh; consuming; producing; decCP
              ; ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9 )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; IoOffers; ⦀-ev-L; ⦀-ev-R; lift-api-node-ev
                 ; absCSc; absBundleG; absNodeA; absNodeB; absNodeC; absNodeD
                 ; coarsenCSc
                 -- (T11) §6e's peer is node D's own BF CLIENT
                 ; absBFc; coarsenBFc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  -- (T11) §6e's fired label is an `apiBF`, so it takes the OTHER `IsApiCSBF`
  using ( ApiHasLink; ahlCS; IsApiCSBF; aicCS; aicBF
        -- (T8c-iii) §9's `cssRowP-noLink` matches the witness at every label, so all
        -- nine constructors are named — without them Agda reads each as a pattern
        -- VARIABLE and the clause silently stops being a dispatch (measured: two
        -- `-WPatternShadowsConstructor` warnings and a type error behind them)
        ; ahlIn; ahlOut; ahlDone; ahlBF; ahlKA; ahlTS; ahlLN; ahlLF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  -- (T11) … and §6e's peer row is the BF client's `bcIdle → bcWrr r`, §6f's the
  -- CS client's VALUE-GATED `ccArf ht → ccIdle`
  using ( aCSc; ceqCSc01; ceqCSc15; aBFc; ceqBFc01 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( ≟-yes-refl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteKaTs blkA
  using ( absBundle-CSc-ev
        -- (T11) §6e's bundle rung, at the BF client instead of the CS one
        ; absBundle-BFc-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA
  using ( ApiIsCons; aicCSreq
        -- (T11) §6e's own consumer tag, and §6f's
        ; aicBFreq; aicCSroll
        ; absNodeA-no-when-D; absNodeB-no-when-D; absNodeC-no-when-D )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( linkBD≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( absBundleG-api-no; drvD-BD-no; drvD-CD-no )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  -- node D's per-leg consume phase and stored block: the LANDED accessors, so
  -- this file adds none of its own (see `dnCScC` below)
  -- (T11b) … and the token's own D-consumer constraint, which §6i's projection
  -- derives at every state in §6h's guard (review C-1)
  using ( TwoLegs; legBD; legCD; phOf; cblkOf; InCp03 )
-- the RELAY driver's per-leg phase accessor — the LANDED one (`LiveDrvBF` reads
-- the same name for `DrvBF`'s Π-bridge), so §4's guard adds no accessor either
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  -- (T11) … and §6e's leg form reads node D's own DOWN-hop BF client at the LANDED
  -- accessor (`LiveChanInv` states the BF channel invariant at this one)
  -- (T11b) … and the LEG PIPELINE INVARIANT itself, with the two relay constraints
  -- §6i's projection refutes: `RelayRfw` is `⊥` wherever `RelayPre` or `RelayFwd`
  -- holds, so a carried token can only sit at `L2`, whose D-consumer constraint IS
  -- `InCp03`.  That is C-1's decoupling, and it is why the api class is
  -- SINGLE-OBJECT
  using ( relayOf; dnClient; PipeInv; L0; L1; L2; L3; L4; RelayPre; RelayFwd )
-- the two LANDED driver-advance relations §5's joint adjacencies are transcribed
-- against (the KEEP-IN-SYNC targets of §5d and §5), and the two LANDED classifiers
-- §5d's extractor delegates to
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ConsAdv; c01; c12; c23; c34; c45; c56
        ; ProdAdv; a01; a12; a23; a34; a45; a56; a67; a78; a89 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkClassify blkA
  using ( consAdv-of; prodAdv-of )
-- (T8c-0) the relay driver's phase ADVANCE: the cone's, because the cone is where the
-- driver's step is (see the note at `relayAdv-leg`).  *** NAME COLLISION, harmless but
-- worth knowing: `LTL/Archive/PipeExposeNodeRelay.agda:103` defines a DIFFERENT
-- `RelayAdv` — the reflexive-transitive closure of `Relay1`, with an `adv-of` TOTAL ON
-- THE SUCCESSOR, i.e. exactly the coarseness §5e's A1 refutes.  Imported by nobody
-- outside `Archive/`, SUPERSEDED; this one is the live object. ***
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiCone blkA
  using ( RelayAdv; raCons; raCp6; raProd
        -- (T8c-ii) §2b⁵'s SHARPENING and its `apiCS`-key pin: the bundle-level fact
        -- "node D's own CS client CO-FIRED", which §6c's producer of `CliDrvAdj` needs
        -- and which no already-applied consequence of the step carries
        ; CsAt; CscCliFired; DnCsRfwLand )
-- (T8c-ii) §4b's three client EDGE pins — the (source , target) pairs `CliDrvAdj`'s
-- three ChainSync rows name.  §6c reads the client's table through these and
-- transcribes none of it
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCSRow blkA
  -- (T8c-iii) §9's `cssRowP-noLink` reads the SERVER's label-directed fact
  using ( CScApiRowP; CSsApiRowP; cscReqEdge; cscRfwEdge; cscDoneEdge )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( hidden )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer blkA
  using ( hiddenMove-⊥; apiNodes-whole )
-- the landed down-hop ChainSync accessors: node D's own CS CLIENT slot (T6b), the
-- relay's CS SERVER slot under `LiveChanCS`'s name, the hop's cell, and the
-- LENIENT unread-message cell predicate §4's narrowed cell arm is built from
-- (`FullMsg`, not `ReqFull` — see `ReqOnly` and the T8 review's I-1).  The six
-- step ADJACENCIES are the landed transcriptions of the two tables, so §5's
-- preservation calculus adds no table of its own
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanCS blkA
  -- (T11, round 3) … and the channel invariant's own client region, which §6h's
  -- record uses as the CONSEQUENT of its three correlations (see the note there:
  -- widening the conclusion is what makes them establishable)
  using ( dnCScOf; dnCSsOf; cellCSDn; FullMsg; rnPayload; CliAwt; CellPreQ
        -- the six step ADJACENCIES, with their constructors: §5 dispatches on
        -- them and transcribes no table of its own
        ; SrvApiAdj; saReq; saFI; saDone; saRF; saRB; saAR; saMRF; saMRB; saIF; saINF
        ; SrvSendAdj; ssRF; ssRB; ssAR; ssIF; ssINF
        ; SrvReadAdj; srReq; srFI; srDone
        ; CliSendAdj; csReq; csFI; csDone
        ; CliReadAdj; crRF; crRB; crAR; crMRF; crMRB; crIF; crINF
        -- (T11b) … the two responder payloads §6i's write classes establish the
        -- cell arms from, and the `full`-cell refutation its two fill classes spend
        ; arPayload; rfPayload; preQ-full-⊥ )

import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) as TLB

------------------------------------------------------------------------
-- §1  NODE D's CS DRIVER-TAIL COUPLING — the shape, and the two funded clauses.
--
-- Read against `LiveDrvBF` §1: this is the SAME object one node over.  Node D
-- runs the SAME `ConsPh` and the SAME `decCons` table as the relay
-- (`decConsD l (consD b ph) = decCons l hi b ph >> Skip`, `SysNode:963-973`), so
-- there is no new phase type and no new table here — only a new PEER slot (node
-- D's own down-hop CS CLIENT, at dir `hi`, `SysNode:984-995`) and a new
-- continuation for the bind (`>> Skip` in place of `>>= λ b′ → produce …`).
--
-- WHY TWO CLAUSES AND NOT SEVEN.  What the `csIdle` refutation consumes is the
-- CLIENT-antecedent reading "the client is at `ccIdle` ⇒ D's driver offers
-- `sendCSRequestNext`", and the way a driver-antecedent coupling delivers that is
-- by REFUTING the other phases at that client position.  With the relay's driver
-- pinned at `cp6`/`pp0`, `PipeInv`'s token pins node D at `{cp0 … cp3}` already
-- (`consP L2 = InCp03`, the gate's §0.6 discount), and the exclusion clause of
-- the gate's §0.5 narrows that to `{cp0, cp1}`; so `cp0` and `cp1` are the only
-- two phases whose clause is load-bearing, and the other five are `⊤` — exactly
-- the way `DrvCp` is `⊤` at the ten shapes no arm names.
--
-- `CliPost` is the `cp1` region and it is io-CLOSED, which is what makes the
-- clause preservable without a cell fact: from `ccWreq` the only row is the
-- client's own write to `ccAwait` (`csCnxt:315-319`), from `ccAwait` the three
-- reply reads land in `{ccArf, ccArb, ccMust}` (`:333-344`), from `ccMust` the
-- two land in `{ccArf, ccArb}` (`:345-352`), and the region's own api exit
-- (`ccArf ht + recvCSRollforward → ccIdle`, `:361-365`) is the step that moves
-- the DRIVER to `cp2`, whose clause is `⊤`.
------------------------------------------------------------------------

-- node D's dn CS client positions that are compatible with its driver having
-- fired `sendCSRequestNext` and not yet `recvCSRollforward` — the `cp1` region
CliPost : NS.CScPos → Set
CliPost NS.ccIdle       = ⊥
CliPost NS.ccWreq       = ⊤
CliPost NS.ccAwait      = ⊤
CliPost (NS.ccWfi ps)   = ⊥
CliPost NS.ccInt        = ⊥
CliPost NS.ccWdone      = ⊥
CliPost NS.ccMust       = ⊤
CliPost (NS.ccArf ht)   = ⊤
CliPost (NS.ccArb pt)   = ⊤
CliPost (NS.ccAif pt)   = ⊥
CliPost (NS.ccAin tp)   = ⊥
CliPost NS.ccTerm       = ⊥

-- `ccIdle` is NOT in the `cp1` region — the one-line refutation the `csIdle`
-- sub-case uses to turn the driver-antecedent coupling into its client-antecedent
-- reading (with `PipeInv`'s `{cp0 … cp3}` and the gate's `{cp0, cp1}` narrowing,
-- a client at `ccIdle` leaves `cp0` as the only phase)
cliPost-idle-⊥ : CliPost NS.ccIdle → ⊥
cliPost-idle-⊥ ()

-- the coupling requirement, per node-D consume sub-phase (total on `ConsPh`)
CliAt : ConsPh → NS.CScPos → Set
CliAt cp0 ca = ca ≡ NS.ccIdle
CliAt cp1 ca = CliPost ca
CliAt cp2 ca = ⊤
CliAt cp3 ca = ⊤
CliAt cp4 ca = ⊤
CliAt cp5 ca = ⊤
CliAt cp6 ca = ⊤

-- the leg's down-hop CS CLIENT (node D's own, dir `hi` — `SysNode:1005-1006`) at
-- its COARSE position.  *** PRODUCER-SITE CHECK: this is `LiveChanCS.dnCScOf`
-- composed with `coarsenCSc`, NOT a new accessor. ***  The campaign has already
-- paid for one duplicate of this kind — `LiveRelayOpen.dnCSs` and
-- `LiveChanCS.dnCSsOf` are the same field under two names and needed the bridge
-- lemma `LiveRelayCS.dnCSs-is-of:366-368` because neither reduces at a variable
-- leg.  Defining this ON TOP of the landed accessor makes a second bridge
-- impossible.  (Node D's consume phase and block likewise already have accessors:
-- `WalkPr.phOf`/`cblkOf`, which is what this file uses.)
dnCScC : TwoLegs → SysState → NS.CScPos
dnCScC l s = coarsenCSc (dnCScOf l s)

-- *** THE COUPLING, in the Π-bridge shape `LiveDrvBF.DrvBF` uses (T1's review
-- ruling: total on the phase type, with the phase supplied as an EXPLICIT
-- argument plus its equation, so that a new `ConsPh` constructor is a coverage
-- error at every consumer rather than a silently-vacuous clause). ***
DrvCliD : TwoLegs → SysState → Set
DrvCliD l s = (x : ConsPh) → phOf l s ≡ x → CliAt x (dnCScC l s)

-- the total dispatch: a `DrvCliD` is built from its two FUNDED clauses and
-- nothing else — the five `⊤` shapes are supplied here, once
drvCliD-of : (l : TwoLegs) (s : SysState)
           → (phOf l s ≡ cp0 → dnCScC l s ≡ NS.ccIdle)
           → (phOf l s ≡ cp1 → CliPost (dnCScC l s))
           → DrvCliD l s
drvCliD-of l s c0 c1 cp0 eq = c0 eq
drvCliD-of l s c0 c1 cp1 eq = c1 eq
drvCliD-of l s c0 c1 cp2 _  = tt
drvCliD-of l s c0 c1 cp3 _  = tt
drvCliD-of l s c0 c1 cp4 _  = tt
drvCliD-of l s c0 c1 cp5 _  = tt
drvCliD-of l s c0 c1 cp6 _  = tt

-- … and the two selectors (the `drvCp-to*` shape: apply the bridge at one
-- sub-phase, so a consumer never has to name the dispatch)
drvCliD-to0 : (l : TwoLegs) (s : SysState) → DrvCliD l s
            → phOf l s ≡ cp0 → dnCScC l s ≡ NS.ccIdle
drvCliD-to0 l s g eq = g cp0 eq

drvCliD-to1 : (l : TwoLegs) (s : SysState) → DrvCliD l s
            → phOf l s ≡ cp1 → CliPost (dnCScC l s)
drvCliD-to1 l s g eq = g cp1 eq

-- BASE — at `SysDecode.initial` node D's two consume drivers are unstepped and
-- its four CS peers are at their `stIdle` heads (`SysNode:1011-1014`), so the
-- `cp0` clause is `refl` and the `cp1` clause is vacuous.  Stated per leg on an
-- EXPLICIT leg argument (the accessors do not reduce at a variable leg)
drvCliD-init : (l : TwoLegs) → DrvCliD l initial
drvCliD-init legBD = drvCliD-of legBD initial (λ _ → refl) (λ ())
drvCliD-init legCD = drvCliD-of legCD initial (λ _ → refl) (λ ())

-- FRAME — the coupling reads exactly two components, so a step fixing both
-- carries it (the shape of `LiveDrvBF.drvBF-frame`; this is what discharges the
-- other leg, the other node, the inert peers and every `break`)
drvCliD-frame : (l : TwoLegs) (s s′ : SysState)
              → phOf l s ≡ phOf l s′ → dnCScC l s ≡ dnCScC l s′
              → DrvCliD l s → DrvCliD l s′
drvCliD-frame l s s′ deq ceq g x eq =
  subst (CliAt x) ceq (g x (subst (λ z → z ≡ x) (sym deq) eq))

------------------------------------------------------------------------
-- §2  *** THE api-SYNC INTRO KIT AT NODE D. ***
--
-- The api hide arithmetic is `LiveRelayOpen` §4's, one node over, and it is worth
-- restating at the point of use because the sibling refusals change: a
-- node-internal `apiES` sync of a peer bundle with its driver lifts to the
-- four-node `⦀` (here `nodes-offer-D`, whose three sibling refusals are the
-- 12-way fingerprint family's node-D row — a CONSUMER tag on a D link, which node
-- A refuses by role and nodes B and C refuse by role-or-link), goes SOLO past the
-- medium because an api event is not in `ioES` (`apiNodes-whole`), and is turned
-- into a τ by the SECOND hide iff it is in `hidden blkA` (`hiddenMove-⊥`).
--
-- TWO KITS AND NOT ONE, for `LiveRelayOpen` §4's reason transposed: node D's two
-- bundles sit on different sides of BOTH of its `⦀`s (the bundle pair AND the
-- driver pair), so leg BD is `⦀-ev-L` twice and leg CD is `⦀-ev-R` twice.  Each
-- kit is generic in the event, the carried value and the bundle's successor.
------------------------------------------------------------------------

-- THE MISSING GENERIC LIFT: node D is the LAST of the four `⦀` operands, so the
-- ladder is three `⦀-ev-R`s.  This is `LiveStableOffer.nodes-offer-BD`'s ladder
-- with the hard-wired `apiBF … recvBFBlock` replaced by the fingerprint the three
-- refusals actually consume — i.e. the event-generic sibling of `nodes-offer-B`
-- and `nodes-offer-C`, which the tree had for the two RELAY nodes and not for D
nodes-offer-D : (s : SysState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X}
  → apiES .mem (X , ee) a
  → ApiIsCons ee × (ApiHasLink linkBD ee ⊎ ApiHasLink linkCD ee)
  → IoOffers (absNodeD (nD s)) ee a
  → IoOffers (absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) ee a
nodes-offer-D s am fp (M , st) =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ st (noOffer→viewV _ (absNodeC-no-when-D (nC s) am fp)))
        (noOffer→viewV _ (absNodeB-no-when-D (nB s) am fp)))
      (noOffer→viewV _ (absNodeA-no-when-D (nA s) am fp))

-- LEG BD (node D's LEFT bundle and LEFT driver, `linkBD` at `(hi, lo)`): the
-- bundle steps, the leg's own consume driver offers the same event, and the two
-- `linkCD` operands are refuted by the link mismatch ⇒ `⊥` from `isStable`
syncD-BD : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {B′ : NetProc}
  → IsApiCSBF ee → ApiHasLink linkBD ee → ApiIsCons ee
  → mem (hidden blkA) (X , ee) a → (ioES .mem (X , ee) a → ⊥)
  → apiES .mem (X , ee) a
  → absBundleG linkBD hi lo
      (SN.NodeStateD.csC-BD (nD (toSys r))) (SN.NodeStateD.csS-BD (nD (toSys r)))
      (SN.NodeStateD.bfC-BD (nD (toSys r))) (SN.NodeStateD.bfS-BD (nD (toSys r)))
      (SN.NodeStateD.inert-BD (nD (toSys r)))
      ─[ ev (evl (evLabel X ee a)) ]─► B′
  → IoOffers (decConsD linkBD (SN.NodeStateD.cons-BD (nD (toSys r)))) ee a
  → isStable (radec r ∖ hidden blkA) → ⊥
syncD-BD r aic ahl aicons hid ¬io am bstep dOff sta =
  hiddenMove-⊥ r hid
    (apiNodes-whole r aic ¬io
      (nodes-offer-D (toSys r) am (aicons , inj₁ ahl)
        ( _
        , lift-api-node-ev _ _ am
            (⦀-ev-L _ _ bstep
              (noOffer→viewV _
                (absBundleG-api-no linkCD hi lo
                   (SN.NodeStateD.csC-CD (nD (toSys r))) (SN.NodeStateD.csS-CD (nD (toSys r)))
                   (SN.NodeStateD.bfC-CD (nD (toSys r))) (SN.NodeStateD.bfS-CD (nD (toSys r)))
                   (SN.NodeStateD.inert-CD (nD (toSys r)))
                   ahl linkBD≢linkCD am)))
            (⦀-ev-L _ _ (proj₂ dOff)
              (noOffer→viewV _ (drvD-CD-no (nD (toSys r)) ahl))))))
    sta

-- LEG CD (both node-D operands are the RIGHT ones, and the sibling pins are the
-- `linkBD` ones)
syncD-CD : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {B′ : NetProc}
  → IsApiCSBF ee → ApiHasLink linkCD ee → ApiIsCons ee
  → mem (hidden blkA) (X , ee) a → (ioES .mem (X , ee) a → ⊥)
  → apiES .mem (X , ee) a
  → absBundleG linkCD hi lo
      (SN.NodeStateD.csC-CD (nD (toSys r))) (SN.NodeStateD.csS-CD (nD (toSys r)))
      (SN.NodeStateD.bfC-CD (nD (toSys r))) (SN.NodeStateD.bfS-CD (nD (toSys r)))
      (SN.NodeStateD.inert-CD (nD (toSys r)))
      ─[ ev (evl (evLabel X ee a)) ]─► B′
  → IoOffers (decConsD linkCD (SN.NodeStateD.cons-CD (nD (toSys r)))) ee a
  → isStable (radec r ∖ hidden blkA) → ⊥
syncD-CD r aic ahl aicons hid ¬io am bstep dOff sta =
  hiddenMove-⊥ r hid
    (apiNodes-whole r aic ¬io
      (nodes-offer-D (toSys r) am (aicons , inj₂ ahl)
        ( _
        , lift-api-node-ev _ _ am
            (⦀-ev-R _ _ bstep
              (noOffer→viewV _
                (absBundleG-api-no linkBD hi lo
                   (SN.NodeStateD.csC-BD (nD (toSys r))) (SN.NodeStateD.csS-BD (nD (toSys r)))
                   (SN.NodeStateD.bfC-BD (nD (toSys r))) (SN.NodeStateD.bfS-BD (nD (toSys r)))
                   (SN.NodeStateD.inert-BD (nD (toSys r)))
                   ahl (λ q → linkBD≢linkCD (sym q)) am)))
            (⦀-ev-R _ _ (proj₂ dOff)
              (noOffer→viewV _ (drvD-BD-no (nD (toSys r)) ahl))))))
    sta

------------------------------------------------------------------------
-- §3  THE TWO OFFERS THE `csIdle` SUB-CASE NEEDS, and the refutation.
--
-- The event is `apiCS l hi sendCSRequestNext` — `consume l d`'s HEAD
-- (`FourNodeDiamond:236-240`), which is why the `cp0` clause of §1 is the one
-- that matters: `decCons l hi b cp0` IS `consume l hi`, a bare `⟶₀` prefix, so
-- the driver's offer is one `sVis` under the `>> Skip` bind and no loop unfolding
-- is involved.
--
-- *** THE "LOOP HEAD" CONCERN WAS ABOUT A LOOP THAT DOES NOT EXIST (the T8
-- review's M-1). ***  `LiveRelayOpen` §8.2 priced a premium for `cp0` being "a LOOP
-- head, not a straight-chain phase".  There is no loop to unfold and there never
-- was: `consume` is a STRAIGHT CHAIN of six api events (`SysNode:920-923` says so
-- in as many words) and neither `consume` nor `consume-k` contains a recursive
-- call (`FourNodeDiamond:224-241`).  The earlier reading — "the recursion in
-- `consume` is through `consume-k`" — invented a loop in order to refute it; the
-- conclusion (zero premium, `cp0`'s decode a literal `⟶₀` prefix) is right and
-- F53 machine-checks it, but the reason is simply that the chain has no back edge.
------------------------------------------------------------------------

-- node D's consume driver at `cp0` fires the api request: the `decCons` step
-- propagates through the `>> Skip` bind, exactly as `consD-offer-recv` does at
-- `cp3` (`LiveStableOffer:810-814`) — link-GENERIC, so `≟-yes-refl` unsticks the
-- `l ≟ l` inside `Net_Api-≟` (the dir test is concrete)
consVis-cp0 : (l : Link) (b₀ : Block₃)
  → viewV (PTree.force (decCons l hi b₀ cp0)) (U.⊤ , apiCS l hi sendCSRequestNext) U.tt
    ≡ just (decCons l hi b₀ cp1)
consVis-cp0 l b₀ rewrite ≟-yes-refl l = refl

-- … and so the whole `consume l hi >> Skip` driver does
consD-offer-req : (l : Link) (b₀ : Block₃)
  → IoOffers (decConsD l (consD b₀ cp0)) (apiCS l hi sendCSRequestNext) U.tt
consD-offer-req l b₀ =
    _
  , TLB.bind-ev (λ _ → Skip) (decCons l hi b₀ cp0) (sVis refl (consVis-cp0 l b₀))

-- the CS CLIENT at a position coarsening to `ccIdle` offers `sendCSRequestNext`
-- (`csCnxt ccIdle`, `NodeSpecs:306-308`; the row is `ceqCSc01`).  This is
-- `LiveRelayOpen.peer-cp5`'s body at the FIRST of `ccIdle`'s three api rows
-- instead of the third
peer-cD0 : (i : Link) (d : Dir) (q : SN.CScPos)
         → coarsenCSc q ≡ NS.ccIdle
         → absCSc i d q ─[ ev (evl (evLabel U.⊤ (apiCS i d sendCSRequestNext) U.tt)) ]─►
           absCSc i d SN.csReqNext1
peer-cD0 i d q pin =
  aCSc i d q SN.csReqNext1
    (subst (λ z → NS.csCfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csCnxt i d z (U.⊤ , apiCS i d sendCSRequestNext) U.tt
                  ≡ just NS.ccWreq)
           (sym pin) (ceqCSc01 i d))

-- *** THE REFUTATION THE GATE's `csIdle` SUB-CASE (4) CONSUMES, leg BD. ***  a
-- STABLE configuration cannot have node D's dn CS client at `ccIdle` while node
-- D's own consume driver is at `cp0`: the client accepts the driver's
-- `sendCSRequestNext`, the sync is node-internal, and the event is hidden by
-- `keptB`'s catch-all (`Spec:109-115`) — `refl`, no block pin needed, because
-- `keptB` keeps only `sendBFBlock`/`recvBFBlock`/`break`
cliIdle-cp0-BD-⊥ : (r : RState) (b₀ : Block₃)
  → coarsenCSc (SN.NodeStateD.csC-BD (nD (toSys r))) ≡ NS.ccIdle
  → SN.NodeStateD.cons-BD (nD (toSys r)) ≡ consD b₀ cp0
  → isStable (radec r ∖ hidden blkA) → ⊥
cliIdle-cp0-BD-⊥ r b₀ pin hcons sta =
  syncD-BD r aicCS ahlCS aicCSreq refl (λ ()) tt
    (absBundle-CSc-ev linkBD hi lo
       (SN.NodeStateD.csC-BD (nD (toSys r))) (SN.NodeStateD.csS-BD (nD (toSys r)))
       (SN.NodeStateD.bfC-BD (nD (toSys r))) (SN.NodeStateD.bfS-BD (nD (toSys r)))
       (SN.NodeStateD.inert-BD (nD (toSys r)))
       {e₁ = CS.apiCSev linkBD hi sendCSRequestNext} {qcc′ = SN.csReqNext1} (λ ()) refl
       (peer-cD0 linkBD hi (SN.NodeStateD.csC-BD (nD (toSys r))) pin))
    (subst (λ q → IoOffers (decConsD linkBD q) (apiCS linkBD hi sendCSRequestNext) U.tt)
           (sym hcons) (consD-offer-req linkBD b₀))
    sta

-- … the CD-leg mirror
cliIdle-cp0-CD-⊥ : (r : RState) (b₀ : Block₃)
  → coarsenCSc (SN.NodeStateD.csC-CD (nD (toSys r))) ≡ NS.ccIdle
  → SN.NodeStateD.cons-CD (nD (toSys r)) ≡ consD b₀ cp0
  → isStable (radec r ∖ hidden blkA) → ⊥
cliIdle-cp0-CD-⊥ r b₀ pin hcons sta =
  syncD-CD r aicCS ahlCS aicCSreq refl (λ ()) tt
    (absBundle-CSc-ev linkCD hi lo
       (SN.NodeStateD.csC-CD (nD (toSys r))) (SN.NodeStateD.csS-CD (nD (toSys r)))
       (SN.NodeStateD.bfC-CD (nD (toSys r))) (SN.NodeStateD.bfS-CD (nD (toSys r)))
       (SN.NodeStateD.inert-CD (nD (toSys r)))
       {e₁ = CS.apiCSev linkCD hi sendCSRequestNext} {qcc′ = SN.csReqNext1} (λ ()) refl
       (peer-cD0 linkCD hi (SN.NodeStateD.csC-CD (nD (toSys r))) pin))
    (subst (λ q → IoOffers (decConsD linkCD q) (apiCS linkCD hi sendCSRequestNext) U.tt)
           (sym hcons) (consD-offer-req linkCD b₀))
    sta

-- the η the two field equations need before `subst` can retarget `decConsD`: a
-- `ConsDPh` IS its two fields (`consCp3⇒form`'s job at `LiveStableOffer:832-839`,
-- stated once here as a record η instead of a seven-clause dispatch, which is
-- available because BOTH fields are given)
consD-η : (x : ConsDPh) {ph : ConsPh} {b : Block₃}
        → cph x ≡ ph → cblk x ≡ b → x ≡ consD b ph
consD-η (consD b ph) refl refl = refl

-- *** THE LEG-DISPATCHED FORM — what T8b consumes. ***  The dispatch is on an
-- EXPLICIT `TwoLegs` argument and never a `with`, for `LiveSrvOpen` §2's reason:
-- at a variable leg the accessors do not reduce, so the two legs cannot share a
-- body even though the two bodies are mirror images
cliIdle-cp0-⊥ : (l : TwoLegs) (r : RState) (b₀ : Block₃)
  → dnCScC l (toSys r) ≡ NS.ccIdle
  → phOf l (toSys r) ≡ cp0
  → cblkOf l (toSys r) ≡ b₀
  → isStable (radec r ∖ hidden blkA) → ⊥
cliIdle-cp0-⊥ legBD r b₀ pin hph hbk =
  cliIdle-cp0-BD-⊥ r b₀ pin (consD-η (SN.NodeStateD.cons-BD (nD (toSys r))) hph hbk)
cliIdle-cp0-⊥ legCD r b₀ pin hph hbk =
  cliIdle-cp0-CD-⊥ r b₀ pin (consD-η (SN.NodeStateD.cons-CD (nD (toSys r))) hph hbk)

------------------------------------------------------------------------
-- §4  *** THE GATE's INVENTORY, MACHINE-CHECKED — the freshness clause and the
-- sharpening. ***
--
-- This section is the T8 gate's §0.5 written as Agda rather than as prose: the
-- four-conjunct clause, the correlation clause, and the case analysis that turns
-- them plus the caller's four refutations into the arms' own equation.  *** WHAT IS
-- PROVED HERE IS THE ANALYSIS, NOT THE ARM: *** all FOUR `csIdle` sub-cases are
-- `⊥`-producing PREMISES of `dnFresh⇒areq`, and all four are THEOREMS at their
-- callers since T8c-ii/iii — the medium's drain τ (`LiveSrvOpen.cellDrainCS-⊥`), the
-- server's own wire READ of the request (`cellReqCS-⊥`, on the io READ ladder
-- `LiveIoIntroCS` §1c + §2b(b)), node D's client's WRITE (`cliWreqCS-⊥`, on §2b(a))
-- and the api SYNC (§3's own `cliIdle-cp0-⊥`, lifted OUT of this lemma at T8c-iii so
-- that `isStable` no longer appears in its signature).
-- *** THE SENTENCE THIS BLOCK USED TO CARRY IS FALSE: *** it said the server's wire
-- READ was "the io landing pin, NOT landed" and node D's client's WRITE needed "a
-- client-side nodes ladder, NOT landed", and called the fourth sub-case discharged
-- here.  Both kits were BUILT by this very range (commit `2731b98`), and the fourth is
-- now a premise like the other three.
--
-- *** ALL THREE PREMISES TOUCH THE MEDIUM, so ALL THREE will want `broken … ≡ false`
-- (the T8 review's M-5 — an earlier note said "two io arms" and undercounted by
-- one). ***  `medDrainτCS-dn` takes an `ebr` argument just as `medOfferInCS` does,
-- and `LiveSrvOpen.csWar-⊥:471-484` threads exactly that.  §3's `cliIdle-cp0-⊥` is
-- the ONE exception in this file: an api sync has no medium operand, so it needs no
-- window.  The hop's cell is one half-duplex place shared by the relay's server at
-- `hi` and node D's client at `hi` — `cellCSDn l s = phase (med s) (dnLink l) hi
-- N2N_ChainSync` (`LiveChanCS:1446-1447`), which is the citation for the sharing
-- (`Base:102-105` is the `Dir` datatype and says nothing about it).
--
-- This is `LiveDrvBF`'s `region⇒stream`/`csRegion⇒must` pattern (`LiveRelayCS`
-- §3): the invariant carries a REGION, and a named sharpening step consumes the
-- stability refutations of everything in the region but the target.  The reason
-- it can be written before the region is CARRIED is that it is pure logic over
-- the two tables — and writing it first is what fixes the interface T8b has to
-- hit.
--
-- WHERE THE CLAUSE WILL LIVE.  The T7 review's §8.3 puts it in `LiveDrvBF.DrvCp`
-- as POSITION clauses at the relay's consume phases.  *** THE GATE FOUND THAT ONE
-- SEPARABILITY CLAIM IN THAT PLAN IS FALSE, and the record belongs here rather
-- than in a report: *** the server conjunct ALONE is not preservable, because
-- `csIdle` has three io READ rows (`NodeSpecs:416-427`) and two of them leave
-- `{csIdle, csAreq}` (to `csAfi ps` and to `csDdone`); refuting those two needs
-- the CELL conjunct, whose own preservation needs the CLIENT conjunct, whose own
-- preservation needs the PHASE conjunct.  Widening the region to the io-closure
-- `{csIdle, csAreq, csAfi _, csDdone, csTerm}` restores preservability and then
-- fails at the OTHER end: `csAfi`/`csDdone`/`csTerm` have no enabled hidden move
-- at `cp6` (the gate's §0.3), so they cannot be sharpened away.  *** So the four
-- conjuncts are one indivisible object and T8b must land them together. ***
--
-- *** AND THE INDIVISIBILITY HAS A SHARPER PROOF THAN THE ONE ABOVE (T8 review
-- §1). ***  Three of the four conjuncts plus the correlation are HOP-LOCAL — the
-- same three components and the same accessors as the landed `ChanCS` — so the
-- obvious cheap move is to add them as fields of `ChanCS` and ride its 107-line
-- preservation calculus and its eight banked row producers.  That FAILS, for a
-- reason recorded in the tree: the client conjunct's exit `ccIdle → ccWdone`
-- (`csCnxt:312-314`) is refutable only by node D's DRIVER never offering
-- `sendCSDone` before `cp5`, which is LEG-LEVEL DRIVER information, and `ChanCS` is
-- by design "no `blkA`, no leg, no link, no driver" (`LiveChanCS:323-324`).  So the
-- trio cannot be absorbed into the driver-free invariant and must live in a
-- leg-level object beside the phase conjunct.  One precision worth carrying: the
-- PHASE conjunct's necessity is ECONOMIC (`{cp2, cp3}` could instead be refuted by
-- node D's BlockFetch api τ, at the price of node D's whole BF driver-tail
-- coupling), while the CELL and CLIENT conjuncts' necessity is LOGICAL.
--
-- *** THE INVENTORY WAS MISSING ONE EXIT STEP, AND IT IS THE ONE THAT MAKES THE
-- CLAUSE CONDITIONAL (the T8 review's I-2). ***  The relay server's own api emit
-- `csAreq + reqCSRequestNext → csCanAwait` (`csSnxt:428-429`) leaves `SrvFresh` and
-- is refuted by NO sibling conjunct and NOT by the phase conjunct (which is about
-- node D's phase).  It is refuted only by the arms' own RELAY-PHASE antecedent —
-- see `RelayFresh` below, which is why the clause is a guarded implication and not
-- a bare conjunction.  This is the `cp4` precedent one level up.
--
-- *** `SrvFresh` IS NOT `LiveChanCS.SrvPre` *** (recommended by the T8 review, and
-- the two are easy to conflate because both are total dispatches on `CSsPos`).  They
-- intersect in `{csAreq}` ALONE: `SrvPre` is the region the server has ENTERED by
-- reading the request and not yet left by a wire-send (`csIdle` is OUT of it,
-- `csCanAwait`/`csAfi`/`csInt`/`csWar` are IN), and `SrvFresh` is the region the
-- relay's DRIVER has not yet advanced (`csIdle` and `csAreq` only).  Nothing
-- transports between them.
--
-- *** TWO CORRECTIONS TO THE GATE's OWN PROSE, kept here because a successor reads
-- the tree and not the reports. ***
--   (a) `csMust` has NO cell fact and NO client fact (`LiveRelayCS` §6(iv)'s
--       four-position sentence is wrong about it): `SrvPre NS.csMust = ⊥`
--       (`LiveChanCS:246`), and `LiveChanCS:231-238` records WHY it must be — F31,
--       adding `csMust` to `SrvPre`, goes RED at `chan-srvSend`'s `ssAR` arm.  The
--       bucket's verdict ("exclude, do not refute") is unaffected and in fact
--       reinforced: with no cell fact the cell may hold the unread
--       `MsgCSAwaitReply`, so at `(csMust , full arPayload , ccAwait)` node D's
--       client could read it (`csMust` would be REFUTABLE, not stuck), and at
--       `(csMust , empty , ccMust)` nothing is enabled.  Either way the position is
--       excluded by `SrvFresh`; do not go hunting for a `ccQui` at `csMust`.
--   (b) "STUCK" is SCOPED to the CS-hop components.  The eleven excluded positions
--       are shown to have no enabled move among the relay's dn CS SERVER, the hop's
--       CELL, node D's dn CS CLIENT and the relay's DRIVER.  The BF axis, the
--       KeepAlive drivers, node A and the up hop are not enumerated, so the honest
--       claim is "not refutable FROM THE FACTS IN HAND", and F54's note should be
--       read with that qualification.
--
-- *** THE `PipeInv` DISCOUNT's ROUTE (the T8 review's I-4). ***  The discount of the
-- gate's §0.6 is real, but the projection route is NOT through `PipeVal`.  `PipeInv`
-- rides `LegJointU`'s FIRST factor, three projections deep: `LegJointU = LegJoint ×
-- PipeVal × KAcFrz × ChanLeg` (`LiveChanJoin:242`), `LegJoint = PipeInvS × LegInv ×
-- TokenExcl` (`LiveLegAssembly:221`), `PipeInvS = PipeInv⁺ × SrvCoupled`
-- (`PipeInvProd:110`), `PipeInv⁺ = PipeInv × Coupled` (`PipeInv:492`).  `PipeVal` is
-- the block-VALUE invariant (`PipeValInv:163-172`) and carries no token at all.
--
-- *** AND THE "SUFFICIENT SET IS UNCHANGED" CLAIM IS NOT ACCURATE (M-2). ***  Two
-- items of the T6-verify §4 list have MOVED, both for the better: its owner decision
-- "widen the channel layer to all thirteen server positions" is REPLACED by the
-- leg-level `SrvFresh` clause below (`LiveChanCS` is untouched and stays scoped to
-- its pre region); and its "the five `csW*` positions ride the layer exactly as
-- `pp2` does" is CORRECTED by the gate, since only `csWar` is in `SrvPre`
-- (`LiveChanCS:249` against `:247-248`, `:250-251`).
------------------------------------------------------------------------

-- the SERVER half: the leg's dn CS server has not yet taken a reply decision —
-- it is waiting for the request or has just read it (`csSnxt`'s `csIdle` reads
-- are the only way in, and its own five wire-sends the only way out)
SrvFresh : NS.CSsPos → Set
SrvFresh NS.csIdle       = ⊤
SrvFresh NS.csAreq       = ⊤
SrvFresh NS.csCanAwait   = ⊥
SrvFresh (NS.csAfi ps)   = ⊥
SrvFresh NS.csInt        = ⊥
SrvFresh NS.csDdone      = ⊥
SrvFresh NS.csMust       = ⊥
SrvFresh (NS.csWrf ht)   = ⊥
SrvFresh (NS.csWrb pt)   = ⊥
SrvFresh NS.csWar        = ⊥
SrvFresh (NS.csWif pt)   = ⊥
SrvFresh (NS.csWin tp)   = ⊥
SrvFresh NS.csTerm       = ⊥

-- the CLIENT half: node D's dn CS client has not yet received a reply (`ccWfi`
-- and `ccWdone` are out because node D's driver offers neither
-- `sendCSFindIntersect` nor — before `cp5` — `sendCSDone`; the four `cc[A..]`
-- emits and `ccMust` are out because they need a RESPONDER payload to have been
-- in the cell, which the cell half forbids).  *** EXACTLY TWO of the nine
-- exclusions rest on the UNOFFERED-LABEL family of §6 — `ccWfi` and `ccWdone`.
-- `ccArb` does NOT (the T8 review's M-5 corrects a report claim that it did): it is
-- ENTERED by the client's io read of `MsgCSRollBackward` (`csCnxt:337-339`) and is
-- refuted by the CELL conjunct, like its three siblings. ***
CliFresh : NS.CScPos → Set
CliFresh NS.ccIdle       = ⊤
CliFresh NS.ccWreq       = ⊤
CliFresh NS.ccAwait      = ⊤
CliFresh (NS.ccWfi ps)   = ⊥
CliFresh NS.ccInt        = ⊥
CliFresh NS.ccWdone      = ⊥
CliFresh NS.ccMust       = ⊥
CliFresh (NS.ccArf ht)   = ⊥
CliFresh (NS.ccArb pt)   = ⊥
CliFresh (NS.ccAif pt)   = ⊥
CliFresh (NS.ccAin tp)   = ⊥
CliFresh NS.ccTerm       = ⊥

-- the PHASE half: node D's own consume driver has not yet received the header.
-- `PipeInv`'s token already gives `{cp0 … cp3}` at the relay's `cp6`/`pp0`
-- (`consP L2 = InCp03`, the gate's §0.6 discount); this narrows it by two
PhFresh : ConsPh → Set
PhFresh cp0 = ⊤
PhFresh cp1 = ⊤
PhFresh cp2 = ⊥
PhFresh cp3 = ⊥
PhFresh cp4 = ⊥
PhFresh cp5 = ⊥
PhFresh cp6 = ⊥

-- *** THE NARROWED UNREAD-REQUEST PREDICATE (the T8 review's I-1). ***  the cell
-- holds node D's unread `MsgCSRequestNext`, and NOT the `MsgCSFindIntersect ps`
-- that `LiveChanCS.ReqFull`'s second disjunct also admits (`:279-281`).  *** THE
-- NARROWING IS WHAT MAKES §4's CLAUSE PRESERVABLE AT ALL: *** with `ReqFull` in the
-- cell arm the state `(csIdle , full (MsgCSFindIntersect ps) , ccAwait)` satisfies
-- the clause, the relay server's `csIdle → csAfi ps` wire READ
-- (`NodeSpecs:420-423`) is ENABLED there, and its successor sits OUTSIDE
-- `SrvFresh` — i.e. `DnFresh` with the wide arm is not an invariant.  Narrowing is
-- SOUND (it does not weaken what the correlation must deliver) because `ccAwait`'s
-- only predecessor is `ccWreq` and `ccWreq`'s only row writes `MsgCSRequestNext`
-- (`csCnxt:315-320`), so an awaiting client's unread message is never a
-- `MsgCSFindIntersect`.  Lenient in `(time , mode , length)`, exactly as the
-- readers' table rows are (`FullMsg`, `LiveChanCS:213-215`)
ReqOnly : SM.CopyPhase → Set
ReqOnly ph = FullMsg ph MsgCSRequestNext

-- the CELL half: the hop's cell holds nothing but, at most, node D's unread
-- `MsgCSRequestNext`.  The three arms are exactly the three the refutation
-- dispatches on
CellFresh : SM.CopyPhase → Set
CellFresh ph = (ph ≡ SM.empty)
             ⊎ (Σ[ x ∈ Payload ] (ph ≡ SM.draining x))
             ⊎ ReqOnly ph

-- an EMPTY cell holds no unread request (the `preQ-full-⊥` shape at the other
-- polarity: `ReqOnly` needs a `full`, and `empty` is not one)
reqOnly-empty-⊥ : ReqOnly SM.empty → ⊥
reqOnly-empty-⊥ (_ , _ , _ , ())

-- … and neither does a DRAINING one.  This is the arm §5's drain class spends: at
-- `(csIdle , draining x , ccAwait)` the correlation itself is contradictory, so the
-- configuration is refuted by the object it is carried in rather than by a move
-- (`LiveChanCS`'s `ccReq` note, one polarity over)
reqOnly-draining-⊥ : (x : Payload) → ReqOnly (SM.draining x) → ⊥
reqOnly-draining-⊥ x (_ , _ , _ , ())

-- *** THE RELAY-PHASE GUARD (the T8 review's I-2 — WITHOUT IT THE CLAUSE IS
-- FALSE). ***  `DnFresh` is NOT an unconditional state invariant: the relay's own
-- api emit at `csAreq` (`csSnxt:428-429`) takes the dn CS server to `csCanAwait`,
-- which is outside `SrvFresh`, and NO sibling conjunct refutes that step — the
-- cell does not move, node D does not move, and the phase conjunct is about node
-- D's phase, not the relay's.  Any ordinary post-emit state is a witness AGAINST
-- the bare conjunction.  What refutes the step is that it is the `apiES` sync with
-- the RELAY's driver, which the same step moves out of the arms' own region: the
-- emit is `produce`'s HEAD event (`FourNodeDiamond:199-202`,
-- `SysNode.decProd … pp0`), so the successor's relay phase is `producing b pp1`.
--
-- Hence the region below — the whole `consuming` half plus `producing _ pp0`,
-- i.e. exactly "the relay has not yet fired `reqCSRequestNext` on the down link".
-- The arms' two sub-phases (`consuming _ cp6`, `producing _ pp0`) are both inside
-- it, so the guard costs the consumer nothing; and the region is BACKWARD-closed
-- along steps (the relay's driver only advances), which is what makes the guarded
-- object preservable — see §5.
--
-- *** THE OTHER CARRYING OPTION IS UNSOUND AS WRITTEN. ***  `LiveRelayCS` §6(iv)
-- offered "carry `DnFresh` as `DrvCp` clauses OR as a new trailing factor"; the
-- second alternative is only sound if the factor is itself phase-guarded, exactly
-- as here.  A bare trailing `DnFresh l s` factor would be a FALSE invariant.
RelayFresh : CPPh → Set
RelayFresh (consuming b x)   = ⊤
RelayFresh (producing b pp0) = ⊤
RelayFresh (producing b pp1) = ⊥
RelayFresh (producing b pp2) = ⊥
RelayFresh (producing b pp3) = ⊥
RelayFresh (producing b pp4) = ⊥
RelayFresh (producing b pp5) = ⊥
RelayFresh (producing b pp6) = ⊥
RelayFresh (producing b pp7) = ⊥
RelayFresh (producing b pp8) = ⊥
RelayFresh (producing b pp9) = ⊥

-- *** THE FRESHNESS CLAUSE's CORE — the gate's §0.5, on FOUR ABSTRACT POSITIONS
-- and no accessor. ***  Stated on the components themselves (the `ChanCS sa ph ca`
-- style, one argument wider) rather than on `(l , s)`, because that is what makes
-- §5's preservation calculus pure table logic: every step class is a statement
-- about the four positions, and the leg, the state and the medium never appear.
-- The fifth field is the CORRELATION the four conjuncts cannot express: an
-- awaiting client facing a still-idle server has its request UNREAD in the cell.
-- It is what closes the last `csIdle` sub-case, and `LiveChanCS`'s `ccReq` is its
-- nearest relative (same establishing step, the client's own write)
record DnFreshC (sa : NS.CSsPos) (ph : SM.CopyPhase) (ca : NS.CScPos)
                (x : ConsPh) : Set where
  constructor mkDnFreshC
  field
    dfSrv  : SrvFresh sa
    dfCli  : CliFresh ca
    dfCell : CellFresh ph
    dfPh   : PhFresh x
    dfArr  : sa ≡ NS.csIdle → ca ≡ NS.ccAwait → ReqOnly ph
open DnFreshC public

-- *** THE CARRIED FORM — the core at the leg's four slots, GUARDED on the relay's
-- phase. ***  (`mkDnFresh` is gone with the un-guarded record: a producer now
-- builds `λ _ → mkDnFreshC …`, and a consumer applies the guard.)
DnFresh : TwoLegs → SysState → Set
DnFresh l s = RelayFresh (relayOf l s)
            → DnFreshC (SStep.coarsenCSs (dnCSsOf l s)) (cellCSDn l s)
                       (dnCScC l s) (phOf l s)

-- the GUARD at the arms' own two sub-phases, so a consumer never has to compute
-- `RelayFresh`: at `consuming _ cp6` it is `⊤` by the whole consuming half, and at
-- `producing _ pp0` by the region's one producing member.  These two are what make
-- the guard free at the point of use
relayFresh-cp6 : (l : TwoLegs) (s : SysState) (b : Block₃)
               → relayOf l s ≡ consuming b cp6 → RelayFresh (relayOf l s)
relayFresh-cp6 l s b eq = subst RelayFresh (sym eq) tt

relayFresh-pp0 : (l : TwoLegs) (s : SysState) (b : Block₃)
               → relayOf l s ≡ producing b pp0 → RelayFresh (relayOf l s)
relayFresh-pp0 l s b eq = subst RelayFresh (sym eq) tt

-- BASE — at `initial` every component is at its head: the server `csIdle`, the
-- client `ccIdle`, the cell `empty`, the phase `cp0`, and the correlation is
-- vacuous because `ccIdle ≢ ccAwait`.  (The relay's driver is at `consuming blkA
-- cp0`, inside the guard — but the base does not need to know that: the guard is
-- discarded)
dnFresh-init : (l : TwoLegs) → DnFresh l initial
dnFresh-init legBD _ = mkDnFreshC tt tt (inj₁ refl) tt (λ _ ())
dnFresh-init legCD _ = mkDnFreshC tt tt (inj₁ refl) tt (λ _ ())

-- THE SERVER-SIDE SHARPENING: inside the fresh region, refuting `csIdle` leaves
-- `csAreq`.  Argument-EXPLICIT and total on `CSsPos`, so the eleven excluded
-- positions are refuted by the region and the twelfth by its premise
srvFresh⇒areq : (q : NS.CSsPos) → SrvFresh q → (q ≡ NS.csIdle → ⊥) → q ≡ NS.csAreq
srvFresh⇒areq NS.csIdle       _  no = ⊥-elim (no refl)
srvFresh⇒areq NS.csAreq       _  _  = refl
srvFresh⇒areq NS.csCanAwait   () _
srvFresh⇒areq (NS.csAfi ps)   () _
srvFresh⇒areq NS.csInt        () _
srvFresh⇒areq NS.csDdone      () _
srvFresh⇒areq NS.csMust       () _
srvFresh⇒areq (NS.csWrf ht)   () _
srvFresh⇒areq (NS.csWrb pt)   () _
srvFresh⇒areq NS.csWar        () _
srvFresh⇒areq (NS.csWif pt)   () _
srvFresh⇒areq (NS.csWin tp)   () _
srvFresh⇒areq NS.csTerm       () _

-- THE CLIENT-SIDE THREE-WAY: the fresh client region has exactly three members,
-- and the refutation needs them as an explicit disjunction to dispatch on
cliFresh-cases : (ca : NS.CScPos) → CliFresh ca
               → (ca ≡ NS.ccIdle) ⊎ (ca ≡ NS.ccWreq) ⊎ (ca ≡ NS.ccAwait)
cliFresh-cases NS.ccIdle       _  = inj₁ refl
cliFresh-cases NS.ccWreq       _  = inj₂ (inj₁ refl)
cliFresh-cases NS.ccAwait      _  = inj₂ (inj₂ refl)
cliFresh-cases (NS.ccWfi ps)   ()
cliFresh-cases NS.ccInt        ()
cliFresh-cases NS.ccWdone      ()
cliFresh-cases NS.ccMust       ()
cliFresh-cases (NS.ccArf ht)   ()
cliFresh-cases (NS.ccArb pt)   ()
cliFresh-cases (NS.ccAif pt)   ()
cliFresh-cases (NS.ccAin tp)   ()
cliFresh-cases NS.ccTerm       ()

-- THE COUPLING's CLIENT-ANTECEDENT READING, at last: inside the fresh phase
-- region a client at `ccIdle` pins node D's driver to `cp0`.  This is the one
-- place §1's `CliPost` earns its keep (F52 is its guard), and it is why the
-- coupling is needed at all: without it `ccIdle` is compatible with `cp1` and the
-- api sync of §3 has no offerer
freshIdle⇒cp0 : (x : ConsPh) (ca : NS.CScPos) → PhFresh x → CliAt x ca
              → ca ≡ NS.ccIdle → x ≡ cp0
freshIdle⇒cp0 cp0 ca _  _    _  = refl
freshIdle⇒cp0 cp1 ca _  post eq = ⊥-elim (cliPost-idle-⊥ (subst CliPost eq post))
freshIdle⇒cp0 cp2 ca () _    _
freshIdle⇒cp0 cp3 ca () _    _
freshIdle⇒cp0 cp4 ca () _    _
freshIdle⇒cp0 cp5 ca () _    _
freshIdle⇒cp0 cp6 ca () _    _

-- *** THE ARMS' EQUATION, FROM THE FRESHNESS CLAUSE AND STABILITY. ***  The three
-- named premises are the three sub-cases whose io/medium kits are T8b's; the
-- fourth sub-case (`empty` cell, client at `ccIdle`) is discharged by §3, and the
-- fifth (`empty`, `ccAwait`) by the correlation field.  *** This is the shape T8b
-- must produce, and the gate's §0.4 inventory is exactly its five arms. ***
dnFresh⇒areq : (l : TwoLegs) (s : SysState)
             -- the GUARD: at the arms' own sub-phases it is `relayFresh-cp6` /
             -- `relayFresh-pp0`, so this argument is free at the point of use
             → RelayFresh (relayOf l s)
             → DnFresh l s → DrvCliD l s
             -- *** (T8c-iii) THE LEMMA IS `RState`-FREE, and that is what lets
             -- `LiveRelayCS` §3 call it. ***  It used to take `r` and `isStable`, but
             -- `isStable` was read in exactly ONE place — §3's `cliIdle-cp0-⊥`, the api
             -- sync of the fourth `csIdle` sub-case — so that use is now the FOURTH
             -- `⊥`-premise below and all four are SysState-level facts the CALLER
             -- proves.  `coAt-split-at` is stated at a `SysState`; without this change
             -- the discharge could not be wired there at all.
             --
             -- (1) the medium's own drain τ — `LiveSrvOpen.cellDrainCS-⊥`
             → (Σ[ x ∈ Payload ] (cellCSDn l s ≡ SM.draining x) → ⊥)
             -- (2) the server's own wire READ of the request — `LiveSrvOpen.cellReqCS-⊥`.
             -- *** (T8c-ii) THE `csIdle` ANTECEDENT IS PART OF THE PREMISE, and it
             -- has to be: *** the read row is `csIdle → csAreq`, so the enabled move
             -- exists only while the server is still idle — which is exactly the case
             -- the dispatch below calls this premise in, and `idle-arms` has the pin
             -- in hand there
             → (SStep.coarsenCSs (dnCSsOf l s) ≡ NS.csIdle → ReqOnly (cellCSDn l s) → ⊥)
             -- (3) node D's client's WRITE into the empty cell — `LiveSrvOpen.cliWreqCS-⊥`
             → (cellCSDn l s ≡ SM.empty → dnCScC l s ≡ NS.ccWreq → ⊥)
             -- (4) (T8c-iii) … and the api SYNC inside node D — §3's own refutation,
             -- lifted out so that `isStable` never appears in this signature
             → (dnCScC l s ≡ NS.ccIdle → phOf l s ≡ cp0 → ⊥)
             → SStep.coarsenCSs (dnCSsOf l s) ≡ NS.csAreq
dnFresh⇒areq l s gate fresh cpl nodrain noread nowrite nosync =
  srvFresh⇒areq (SStep.coarsenCSs (dnCSsOf l s)) (dfSrv fr) idle-⊥
  where
  fr = fresh gate
  -- the `empty` arm, over the client's three fresh positions.  BOTH dispatches
  -- take their disjunction as an EXPLICIT argument rather than through a `with`,
  -- for `LiveRelayCS` §3's reason (a `with` here would abstract a type mentioning
  -- an imported `blkA`-parameterised predicate) — the `csWar-⊥` `arms` idiom
  empty-arms : cellCSDn l s ≡ SM.empty
             → SStep.coarsenCSs (dnCSsOf l s) ≡ NS.csIdle
             → (dnCScC l s ≡ NS.ccIdle)
               ⊎ (dnCScC l s ≡ NS.ccWreq)
               ⊎ (dnCScC l s ≡ NS.ccAwait)
             → ⊥
  empty-arms he hidl (inj₁ hci) =
    nosync hci
      (freshIdle⇒cp0 (phOf l s) (dnCScC l s) (dfPh fr) (cpl (phOf l s) refl) hci)
  empty-arms he hidl (inj₂ (inj₁ hcw)) = nowrite he hcw
  empty-arms he hidl (inj₂ (inj₂ hca)) =
    reqOnly-empty-⊥ (subst ReqOnly he (dfArr fr hidl hca))
  -- … and the three-armed cell dispatch it sits inside
  idle-arms : SStep.coarsenCSs (dnCSsOf l s) ≡ NS.csIdle
            → CellFresh (cellCSDn l s) → ⊥
  idle-arms hidl (inj₁ he) =
    empty-arms he hidl (cliFresh-cases (dnCScC l s) (dfCli fr))
  idle-arms hidl (inj₂ (inj₁ hdr)) = nodrain hdr
  idle-arms hidl (inj₂ (inj₂ hrq)) = noread hidl hrq
  idle-⊥ : SStep.coarsenCSs (dnCSsOf l s) ≡ NS.csIdle → ⊥
  idle-⊥ hidl = idle-arms hidl (dfCell fr)

------------------------------------------------------------------------
-- §5  *** THE PRESERVATION CALCULUS — one lemma per step class. ***
--
-- Read against `LiveChanCS` §5, which is this calculus one component short and one
-- guard short.  Two structural decisions, both of them what keeps the section
-- table logic rather than state plumbing:
--
--   (a) *** THE CORE IS STATED ON FOUR ABSTRACT POSITIONS *** (`DnFreshC sa ph ca
--       x`), so every class lemma is a pure statement about `csSnxt`/`csCnxt` and
--       the two driver chains.  The leg, the state, the medium and the accessors
--       appear only in the thin state-level wrappers at the end, all of which go
--       through ONE lift.
--   (b) *** THE GUARD IS HANDLED IN THREE WAYS, NOT TWO — the landed truth after
--       C-1. ***  Every class that FIXES the relay's phase transports the guard by a
--       `subst`, so its preservation IS the core's (`dnFresh-lift`); that covers node
--       D's api sync, the four io classes, the drain and the frame.  The relay's own
--       advance splits: on its UP-link consume chain the SOURCE is inside the region
--       and `RelayFresh` is `⊤` there, so the guard needs no transport at all
--       (`dnFresh-relayCons`), and on every DOWN-link advance the SUCCESSOR is outside
--       the region, so the obligation is vacuous (`dnFresh-relayOut`).  `relayAdv-guard`
--       is the total dispatch between those two, and `RelayAdv` — whose `raCp6` row IS
--       the `cp6` down-link landing — is what makes it total.  (The first shipment had
--       only the second of the three and described the relay side as "every class but
--       ONE fixes the phase, the exception is refuted at the successor"; that reading
--       had no class for the consume chain at all, which is what C-3(a) was.)
--
-- *** WHY THE TWO JOINT ADJACENCIES. ***  A CS peer's api row and its driver's phase
-- advance are two halves of ONE step: `apiCS l d …` ∈ `apiES`, so the peer cannot
-- fire alone inside its node.  The two objects below therefore index the peer's row
-- and the driver's phase pair TOGETHER (`CliDrvAdj` on node D's side, keyed on both;
-- on the relay's side the phase pair alone suffices and is `LiveLegApiCone.RelayAdv`,
-- because what the class needs of the server is only that the relay LEFT the region).
-- Splitting them
-- would make the calculus unprovable: at node D's `cp1` the client's `caReq` row and
-- the driver's `c12` advance are individually consistent and jointly impossible.
--
-- *** WHAT THE JOINT DATATYPES CLAIM, AND WHERE IT IS CHECKED. ***  Being
-- hypothesis-position objects they are safe if too WIDE and vacuous if too NARROW —
-- the `LiveChanCS` §4 hazard.  `CliDrvAdj`'s completeness is the content of §6: its
-- three CS rows are `consume`'s three CS api events and no others, because node D's
-- driver never offers `sendCSFindIntersect` at any phase and offers `sendCSDone`
-- only at `cp5`, which §6/§6b prove rather than assert.
--
-- *** AND THE RELAY SIDE IS NO LONGER A COMPLETENESS ARGUMENT AT ALL — it is an
-- EXTRACTION, which is the strongest form this claim can take. ***  The sentence that
-- used to stand here — "`RelayCsAdj`'s completeness is read straight off `produce`: its
-- first three events are its only `apiCS` ones, and the relay's CONSUMING half fires on
-- the UP link, which cannot move the down hop's server at all" — is *** FALSE, and it is
-- the defect C-1 was: *** the `cp6`/`pp0` collapse makes the consuming half fire
-- `produce`'s HEAD on the DOWN link, landing at `producing _ pp1`.  `RelayAdv` replaced
-- that three-row object and its completeness is now MACHINE-CHECKED, not argued:
-- `cpStepKindQ-of⁺` (`LiveLegApiCone`) is total on `CPPh` and answers EVERY clause with a
-- `RelayAdv`, so a missing row is a coverage error at the classifier rather than a
-- silently vacuous class downstream.  F61 blocks the false sentence's reintroduction.
------------------------------------------------------------------------

-- transport the core along equalities of its four components — what every frame
-- and every fixity hypothesis hands over.  One clause, so the state-level wrappers
-- below never `subst` field by field
dnFreshC-cong : (sa sa′ : NS.CSsPos) (ph ph′ : SM.CopyPhase)
                (ca ca′ : NS.CScPos) (x x′ : ConsPh)
              → sa ≡ sa′ → ph ≡ ph′ → ca ≡ ca′ → x ≡ x′
              → DnFreshC sa ph ca x → DnFreshC sa′ ph′ ca′ x′
dnFreshC-cong sa _ ph _ ca _ x _ refl refl refl refl fr = fr

-- inside `CellFresh` a FULL cell holds the request and NOTHING else: the `empty`
-- and `draining` arms are constructor clashes.  This is the single fact all four
-- io READ classes spend, so none of them needs a per-message clause
cellFresh-full : (y : Payload) → CellFresh (SM.full y) → ReqOnly (SM.full y)
cellFresh-full y (inj₁ ())
cellFresh-full y (inj₂ (inj₁ (_ , ())))
cellFresh-full y (inj₂ (inj₂ rq)) = rq

-- … and `ReqOnly` PINS the message, so any other one is refuted.  Generic in the
-- message and in `(time , mode , length)`, exactly as `FullMsg` is: the caller
-- supplies the one-line constructor clash for its own row
reqOnly-not : (t : Time) (md : Mode) (ln : Length) (mc : MessageChainSync)
            → (mc ≡ MsgCSRequestNext → ⊥)
            → ReqOnly (SM.full (t , md , ln , chainSync mc)) → ⊥
reqOnly-not t md ln mc no (_ , _ , _ , refl) = no refl

-- the cell the client's REQUEST wire-send leaves behind IS a `ReqOnly` cell — the
-- one place the correlation `dfArr` is ESTABLISHED rather than spent
reqOnly-rn : ReqOnly (SM.full rnPayload)
reqOnly-rn = _ , _ , _ , refl

-- *** THE ROW CUT ON THE SERVER's api CLASS — the machine-checked half of the
-- review's I-2. ***  Inside the fresh region the ONLY api row the dn CS server can
-- fire is `saReq`, and it LEAVES the region: nine of the ten rows are refuted by the
-- SOURCE's own membership, and the tenth is refuted by nothing hop-local.  That is
-- why the object is GUARDED — and why the guard has to be dispatched over the relay's
-- whole phase axis (`RelayAdv`/`relayAdv-guard`) rather than over a hand-picked row set
srvApi-fresh : (sa sa′ : NS.CSsPos) → SrvApiAdj sa sa′ → SrvFresh sa
             → (sa ≡ NS.csAreq) × (sa′ ≡ NS.csCanAwait)
srvApi-fresh _ _ saReq      _  = refl , refl
srvApi-fresh _ _ (saFI _)   ()
srvApi-fresh _ _ saDone     ()
srvApi-fresh _ _ (saRF _)   ()
srvApi-fresh _ _ (saRB _)   ()
srvApi-fresh _ _ saAR       ()
srvApi-fresh _ _ (saMRF _)  ()
srvApi-fresh _ _ (saMRB _)  ()
srvApi-fresh _ _ (saIF _)   ()
srvApi-fresh _ _ (saINF _)  ()

-- *** (T8c-0) THE RELAY DRIVER's PHASE AXIS NOW COMES FROM THE CONE. ***  `RelayAdv`
-- and a standalone extractor `relayAdv-of` were defined HERE in the T8b fix round;
-- both have MOVED to `LiveLegApiCone`, and the extractor did not survive as a separate
-- lemma — it is now `cpStepKindQ-of⁺`'s EIGHTEENTH component, so the advance and the
-- classifier's `x′` are SINGLE-SOURCED and cannot drift between two dispatches (two
-- independent dispatches on the same phase produce equal `x′` terms, but a `with`-
-- abstracted consumer cannot see that, which is why the component route is the only
-- one that typechecks).  `LiveLegApiExpose.DriverExposed⁺` carries it out as
-- `deRelayAdvBD`/`-CD`.  Keeping a second local copy of the datatype would have been
-- the duplicate-object defect the campaign has already paid for once.
--
-- What stays here is what consumes it: the guard's total dispatch and the two step
-- classes.  *** C-1's row is `raCp6` and it is the cone's now — F61 re-aimed
-- accordingly (§7b). ***

-- the per-leg selector: `relayOf legBD s` IS `cp-B (nB s)` definitionally, so the
-- cone's two node-stated fields ARE this leg-stated fact and the dispatch is pure
-- selection (the `chanUp-of`/`chanDn-of` idiom)
relayAdv-leg : (l : TwoLegs) (s s′ : SysState)
             → ((relayOf legBD s ≡ relayOf legBD s′)
                ⊎ RelayAdv (relayOf legBD s) (relayOf legBD s′))
             → ((relayOf legCD s ≡ relayOf legCD s′)
                ⊎ RelayAdv (relayOf legCD s) (relayOf legCD s′))
             → (relayOf l s ≡ relayOf l s′) ⊎ RelayAdv (relayOf l s) (relayOf l s′)
relayAdv-leg legBD s s′ fbd fcd = fbd
relayAdv-leg legCD s s′ fbd fcd = fcd

-- *** THE GUARD's TOTAL DISPATCH ON A RELAY ADVANCE — the fix round's C-3 repair. ***
-- For EVERY relay advance, either the SOURCE is in the relay's own consuming half (so
-- `RelayFresh` is `⊤` there and the guard transports for free) or the SUCCESSOR is
-- OUTSIDE the guard (so the obligation is vacuous).  *** Total on `RelayAdv`, so no
-- advance family is missed *** — which is precisely what the three-row `RelayCsAdj`
-- could not say, and why the calculus was short of three step families on this axis.
-- Note that every `raProd` successor is `pp1`-or-later and so is `raCp6`'s: the whole
-- DOWN-link half of the relay's chain is out of the region, and the whole UP-link half
-- is inside it
relayAdv-guard : (x x′ : CPPh) → RelayAdv x x′
               → (Σ[ b ∈ Block₃ ] Σ[ c ∈ ConsPh ] (x ≡ consuming b c))
                 ⊎ (RelayFresh x′ → ⊥)
relayAdv-guard _ _ (raCons b _ c _ _)  = inj₁ (b , c , refl)
relayAdv-guard _ _ (raCp6 _)           = inj₂ (λ ())
relayAdv-guard _ _ (raProd _ _ _ a01)  = inj₂ (λ ())
relayAdv-guard _ _ (raProd _ _ _ a12)  = inj₂ (λ ())
relayAdv-guard _ _ (raProd _ _ _ a23)  = inj₂ (λ ())
relayAdv-guard _ _ (raProd _ _ _ a34)  = inj₂ (λ ())
relayAdv-guard _ _ (raProd _ _ _ a45)  = inj₂ (λ ())
relayAdv-guard _ _ (raProd _ _ _ a56)  = inj₂ (λ ())
relayAdv-guard _ _ (raProd _ _ _ a67)  = inj₂ (λ ())
relayAdv-guard _ _ (raProd _ _ _ a78)  = inj₂ (λ ())
relayAdv-guard _ _ (raProd _ _ _ a89)  = inj₂ (λ ())

-- *** NODE D's OWN api SYNC, as the pair the event determines. ***  Six rows: the
-- three CS ones move the client and the driver together, and the three BF ones move
-- the driver with the CS client FIXED (`consume`'s six api events are three CS and
-- three BF — `FourNodeDiamond:224-241`).  There is no seventh: a client api row
-- without a driver advance would be a peer firing alone inside an `apiES` sync, and
-- the client's four remaining rows carry labels the driver never offers here (§6).
--
-- *** KEEP IN SYNC — `LiveChanCS.CliApiAdj:430-437` (the client's seven api rows) ×
-- `WalkMeasure.ConsAdv:274-280` (the driver's six hops).  This datatype is the PAIRING
-- of those two tables and it is a TRANSCRIPTION, not a derivation: if either table
-- gains a row, this one must be re-derived.  C-1 (at `RelayAdv` above) is what a
-- mis-transcription of the sibling table costs. ***
--
-- *** THE FOUR OMITTED `CliApiAdj` ROWS, AND WHY EACH IS OMITTED (the fix round's
-- I-1, recorded here as `LiveChanCS` §4 records its own omission). ***  A row is
-- omitted only when its LABEL is one node D's driver provably never fires at a phase
-- the omission matters, and each justification is a machine-checked member of §6/§6b.
--
-- *** THE OBLIGATION T8c-0 LEFT OPEN HERE IS CLOSED (T8c-ii) — §6c IS ITS PRODUCER,
-- TOTAL ON THE DRIVER'S SIX HOPS. ***  What was open, kept because it says exactly what
-- the closure had to supply: this datatype was producible from the cone at every
-- combination BUT ONE, `(ConsAdv cp0 cp1 , the CS client's row-fact in its FIXITY arm)`.
-- `dnFresh-cliApi` CARRIED that case (the successor core IS the source core and
-- `PhFresh cp1` holds), so `DnFresh` did not need it; `drvCliD-api-at` CANNOT (at `cp0`
-- the coupling pins the client to `ccIdle`, fixity carries `ccIdle` across, and
-- `CliAt cp1 ccIdle = CliPost ccIdle = ⊥`).  The state is UNREACHABLE — the driver fires
-- `sendCSRequestNext` and node D's client at `ccIdle` must co-fire — but *** "the client
-- co-fired" is a BUNDLE-level fact and neither the fired label nor the driver's step
-- supplies it. ***  So the missing datum was a SHARPENING, not a threading, and it
-- landed as `LiveLegApiCone` §2b⁵: at an `apiCS` label on the CS CLIENT's own key the
-- bundle reports the GENUINE ROW, refuted in the server-fired arm by the direction
-- clash `cl ≢ sv`.  §6c's `cliDrvAdj-of` reads it, and the fixity arm is never consulted
-- at the three ChainSync hops.  *** WIDENING `CliAt cp1` WAS NOT AN ESCAPE and still is
-- not: *** F52 shows `cliPost-idle-⊥` is load-bearing, through `freshIdle⇒cp0`, on this
-- file's own goal `dnFresh⇒areq`.
--
-- the four omitted rows:
--   · `caFI`     (`ccIdle → ccWfi ps`, `sendCSFindIntersect`) — `consD-no-fi`, the
--                label is absent from `consume` at EVERY phase;
--   · `caRecvB`  (`ccArb pt → ccIdle`, `recvCSRollback`) — `consD-no-rb`, likewise;
--   · `caRecvIF` (`ccAif pt → ccIdle`, `recvCSIntersectFound`) — `consD-no-if`;
--   · `caRecvIN` (`ccAin tp → ccIdle`, `recvCSIntersectNotFound`) — `consD-no-in`.
-- `caDone` IS here, as `cdDone` at its one real phase pair `cp5 → cp6`; outside the
-- fresh region that is all the object needs, and `consD-no-done` covers the two fresh
-- phases.  *** AND NOTE WHY THE FOUR CANNOT SIMPLY BE ADDED "AT A GENERIC ADVANCE",
-- which the review recommended: *** a generic-advance row leaves the successor phase
-- free, and `dnFresh-cliApi` closes each row by EITHER the client conjunct (source
-- outside `CliFresh`) or the phase conjunct (successor outside `PhFresh`).  `caFI`'s
-- source is `ccIdle`, which IS in `CliFresh`, so its only closure is the phase — and a
-- free successor phase gives none; the three `caRecv*` rows would likewise break
-- `drvCliD-api-at`, whose `cp1` clause needs a KNOWN successor phase.  So the honest
-- form is the one landed: omit, and justify each omission by a proof.
data CliDrvAdj : NS.CScPos → ConsPh → NS.CScPos → ConsPh → Set where
  cdReq   : CliDrvAdj NS.ccIdle cp0 NS.ccWreq cp1              -- sendCSRequestNext
  cdRecvF : (ht : Header × Tip)
          → CliDrvAdj (NS.ccArf ht) cp1 NS.ccIdle cp2          -- recvCSRollforward
  cdDone  : CliDrvAdj NS.ccIdle cp5 NS.ccWdone cp6             -- sendCSDone
  cdBF23  : (ca : NS.CScPos) → CliDrvAdj ca cp2 ca cp3         -- sendBFRequestRange
  cdBF34  : (ca : NS.CScPos) → CliDrvAdj ca cp3 ca cp4         -- recvBFBlock
  cdBF45  : (ca : NS.CScPos) → CliDrvAdj ca cp4 ca cp5         -- sendBFClientDone

-- (1) *** NODE D's api CLASS. ***  The relay's server and the hop's cell are fixed.
-- ONE row survives — `cdReq`, which moves `(ccIdle , cp0)` to `(ccWreq , cp1)`,
-- both inside their regions, and whose successor is not `ccAwait` so the
-- correlation is vacuous.  `cdRecvF` is refuted by the CLIENT conjunct (its source
-- `ccArf ht` is outside `CliFresh`) and the other four by the PHASE conjunct
dnFresh-cliApi : (sa : NS.CSsPos) (ph : SM.CopyPhase) (ca ca′ : NS.CScPos)
                 (x x′ : ConsPh)
               → CliDrvAdj ca x ca′ x′
               → DnFreshC sa ph ca x → DnFreshC sa ph ca′ x′
dnFresh-cliApi sa ph _ _ _ _ cdReq       fr =
  mkDnFreshC (dfSrv fr) tt (dfCell fr) tt (λ _ ())
dnFresh-cliApi sa ph _ _ _ _ (cdRecvF _) fr = ⊥-elim (dfCli fr)
dnFresh-cliApi sa ph _ _ _ _ cdDone      fr = ⊥-elim (dfPh fr)
dnFresh-cliApi sa ph _ _ _ _ (cdBF23 _)  fr = ⊥-elim (dfPh fr)
dnFresh-cliApi sa ph _ _ _ _ (cdBF34 _)  fr = ⊥-elim (dfPh fr)
dnFresh-cliApi sa ph _ _ _ _ (cdBF45 _)  fr = ⊥-elim (dfPh fr)

-- (2) THE io FILL BY THE SERVER — the cell goes `empty → full y`.  All five
-- wire-send rows start OUTSIDE `SrvFresh` (the five `csW*` positions), so the class
-- is refuted by the server conjunct alone, one body five times
dnFresh-srvSend : (sa sa′ : NS.CSsPos) (y : Payload) (ca : NS.CScPos) (x : ConsPh)
                → SrvSendAdj sa y sa′
                → DnFreshC sa SM.empty ca x → DnFreshC sa′ (SM.full y) ca x
dnFresh-srvSend _ _ _ ca x (ssRF _ _)  fr = ⊥-elim (dfSrv fr)
dnFresh-srvSend _ _ _ ca x (ssRB _ _)  fr = ⊥-elim (dfSrv fr)
dnFresh-srvSend _ _ _ ca x ssAR        fr = ⊥-elim (dfSrv fr)
dnFresh-srvSend _ _ _ ca x (ssIF _ _)  fr = ⊥-elim (dfSrv fr)
dnFresh-srvSend _ _ _ ca x (ssINF _)   fr = ⊥-elim (dfSrv fr)

-- (3) *** THE io FILL BY THE CLIENT — the ONE step that ESTABLISHES the
-- correlation. ***  Its request row takes `(ccWreq , empty)` to `(ccAwait , full
-- rnPayload)`, which is both the narrowed cell arm and the correlation's conclusion;
-- its other two rows start outside `CliFresh`
dnFresh-cliSend : (sa : NS.CSsPos) (y : Payload) (ca ca′ : NS.CScPos) (x : ConsPh)
                → CliSendAdj ca y ca′
                → DnFreshC sa SM.empty ca x → DnFreshC sa (SM.full y) ca′ x
dnFresh-cliSend sa _ _ _ x csReq    fr =
  mkDnFreshC (dfSrv fr) tt (inj₂ (inj₂ reqOnly-rn)) (dfPh fr) (λ _ _ → reqOnly-rn)
dnFresh-cliSend sa _ _ _ x (csFI _) fr = ⊥-elim (dfCli fr)
dnFresh-cliSend sa _ _ _ x csDone   fr = ⊥-elim (dfCli fr)

-- (4) *** THE SERVER's WIRE-READ — the step the arms' own equation names. ***  The
-- cell is `full`, so `cellFresh-full` pins its message to `MsgCSRequestNext`: the
-- `MsgCSFindIntersect` and `MsgCSDone` rows are refuted by that pin (*** this is
-- precisely the review's I-1 — with the WIDE `ReqFull` cell arm the first of them
-- would be ENABLED and would land the server outside the region ***), and the
-- request row lands at `csAreq`, inside `SrvFresh`, with the cell `draining` and the
-- correlation vacuous
dnFresh-srvRead : (sa sa′ : NS.CSsPos) (y : Payload) (ca : NS.CScPos) (x : ConsPh)
                → SrvReadAdj sa y sa′
                → DnFreshC sa (SM.full y) ca x → DnFreshC sa′ (SM.draining y) ca x
dnFresh-srvRead _ _ _ ca x srReq    fr =
  -- the correlation is vacuous at `csAreq`, so ONE absurd argument closes it (an
  -- absurd pattern has to be the LAST in an extended λ — `λ () _` is a parse error)
  mkDnFreshC tt (dfCli fr) (inj₂ (inj₁ (_ , refl))) (dfPh fr) (λ ())
dnFresh-srvRead _ _ _ ca x (srFI _) fr =
  ⊥-elim (reqOnly-not _ _ _ _ (λ ()) (cellFresh-full _ (dfCell fr)))
dnFresh-srvRead _ _ _ ca x srDone   fr =
  ⊥-elim (reqOnly-not _ _ _ _ (λ ()) (cellFresh-full _ (dfCell fr)))

-- (5) THE CLIENT's WIRE-READ — all seven rows refuted.  The three from `ccAwait`
-- carry RESPONDER messages, which the cell pin excludes; the four from
-- `ccMust`/`ccInt` start outside `CliFresh`
dnFresh-cliRead : (sa : NS.CSsPos) (y : Payload) (ca ca′ : NS.CScPos) (x : ConsPh)
                → CliReadAdj ca y ca′
                → DnFreshC sa (SM.full y) ca x → DnFreshC sa (SM.draining y) ca′ x
dnFresh-cliRead sa _ _ _ x (crRF _ _)  fr =
  ⊥-elim (reqOnly-not _ _ _ _ (λ ()) (cellFresh-full _ (dfCell fr)))
dnFresh-cliRead sa _ _ _ x (crRB _ _)  fr =
  ⊥-elim (reqOnly-not _ _ _ _ (λ ()) (cellFresh-full _ (dfCell fr)))
dnFresh-cliRead sa _ _ _ x crAR        fr =
  ⊥-elim (reqOnly-not _ _ _ _ (λ ()) (cellFresh-full _ (dfCell fr)))
dnFresh-cliRead sa _ _ _ x (crMRF _ _) fr = ⊥-elim (dfCli fr)
dnFresh-cliRead sa _ _ _ x (crMRB _ _) fr = ⊥-elim (dfCli fr)
dnFresh-cliRead sa _ _ _ x (crIF _ _)  fr = ⊥-elim (dfCli fr)
dnFresh-cliRead sa _ _ _ x (crINF _)   fr = ⊥-elim (dfCli fr)

-- (6) *** THE MEDIUM's OWN DRAIN τ — and the one class where the correlation is
-- spent on its OWN source state. ***  `draining y → empty` keeps every position, and
-- the successor's correlation would need `ReqOnly empty`; the SOURCE's correlation
-- already says `ReqOnly (draining y)`, which is false, so `(csIdle , draining y ,
-- ccAwait)` is refuted by the object it is carried in rather than by a move.  This
-- is `LiveChanCS`'s `ccReq` note at the other polarity
dnFresh-drain : (sa : NS.CSsPos) (y : Payload) (ca : NS.CScPos) (x : ConsPh)
              → DnFreshC sa (SM.draining y) ca x → DnFreshC sa SM.empty ca x
dnFresh-drain sa y ca x fr =
  mkDnFreshC (dfSrv fr) (dfCli fr) (inj₁ refl) (dfPh fr)
             (λ hs hc → ⊥-elim (reqOnly-draining-⊥ y (dfArr fr hs hc)))

------------------------------------------------------------------------
-- §5b  THE STATE-LEVEL WRAPPERS.  One lift, and one class that is not a lift.
------------------------------------------------------------------------

-- *** THE LIFT. ***  Every class but the relay's own api sync fixes the relay's
-- phase, so the guard transports BACKWARDS along the step and the guarded object's
-- preservation is exactly the core's.  This is the lemma that makes §5 reusable
dnFresh-lift : (l : TwoLegs) (s s′ : SysState)
             → relayOf l s ≡ relayOf l s′
             → (DnFreshC (SStep.coarsenCSs (dnCSsOf l s)) (cellCSDn l s)
                         (dnCScC l s) (phOf l s)
                → DnFreshC (SStep.coarsenCSs (dnCSsOf l s′)) (cellCSDn l s′)
                           (dnCScC l s′) (phOf l s′))
             → DnFresh l s → DnFresh l s′
dnFresh-lift l s s′ peq step fr g′ = step (fr (subst RelayFresh (sym peq) g′))

-- FRAME — the four components fixed (the other leg, the other node, every inert
-- peer, every `break`, and every medium τ on another channel)
dnFresh-frame : (l : TwoLegs) (s s′ : SysState)
              → relayOf l s ≡ relayOf l s′
              → dnCSsOf l s ≡ dnCSsOf l s′
              → cellCSDn l s ≡ cellCSDn l s′
              → dnCScOf l s ≡ dnCScOf l s′
              → phOf l s ≡ phOf l s′
              → DnFresh l s → DnFresh l s′
dnFresh-frame l s s′ peq seq heq keq deq =
  dnFresh-lift l s s′ peq
    (dnFreshC-cong _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) heq
                   (cong coarsenCSc keq) deq)

-- *** THE RELAY's OWN ADVANCE, IN THE TWO SHAPES `relayAdv-guard` HANDS OUT. ***
-- These two are the fix round's C-3(a)/(b)/(c) classes, and together with
-- `relayAdv-guard`'s totality they cover EVERY relay advance.
--
-- (a) the relay advanced INSIDE the region — its own UP-link consume chain, all six
-- hops.  Our four components are fixed there (the event is on the other hop), and the
-- guard is `⊤` at the SOURCE for free, so nothing has to be transported BACKWARDS.
-- This is the class the first shipment had no analogue of at all, and the reason it
-- needs no phase PAIR is that `RelayFresh` is constant on the consuming half
-- *** THE FOUR-FIXITY PRECONDITION, and where each fixity comes from (the fix-round
-- review's I-4). ***  This class is proved MODULO its four component fixities, so "the
-- relay's axis is dischargeable" is true only once they arrive.  They do, and unevenly:
-- `cellCSDn l s = phase (med s) (dnLink l) hi N2N_ChainSync` (`LiveChanCS:1447`) is a pure
-- function of `med s`, so `DriverExposed⁺.deMed` gives it by ONE `cong` — free; the other
-- three (the dn CS server, node D's CS client, node D's phase) come from the FIXITY ARMS
-- of `deCSRowsBD`'s server component, `deCSDnCliBD`/`-CD` and `deConsStepBD`/`-CD`, which
-- means a carry must dispatch on WHICH NODE FIRED.  That dispatch is sound because only
-- one node fires per api step (the four nodes compose with `⦀` over `∅ESa`, so
-- `driverExpose⁺`'s six arms are exclusive), and it is ≈20-40 of the carry — named here
-- so it is not discovered late.
dnFresh-relayCons : (l : TwoLegs) (s s′ : SysState) (b : Block₃) (c : ConsPh)
                  → relayOf l s ≡ consuming b c
                  → dnCSsOf l s ≡ dnCSsOf l s′
                  → cellCSDn l s ≡ cellCSDn l s′
                  → dnCScOf l s ≡ dnCScOf l s′
                  → phOf l s ≡ phOf l s′
                  → DnFresh l s → DnFresh l s′
dnFresh-relayCons l s s′ b c req seq heq keq deq fr _ =
  dnFreshC-cong _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) heq
                (cong coarsenCSc keq) deq
    (fr (subst RelayFresh (sym req) tt))

-- (b)+(c) the relay advanced OUT of the region — every DOWN-link advance, i.e. the
-- `cp6` bind hop and all nine produce hops.  The obligation is vacuous, so the class
-- demands nothing else: the components may move freely.  *** THIS IS THE PHASE GUARD
-- DOING ITS ENTIRE JOB *** — the `csAreq → csCanAwait` exit no sibling conjunct
-- reaches (review I-2), now at the `cp6` sub-phase too (fix round C-1)
dnFresh-relayOut : (l : TwoLegs) (s s′ : SysState)
                 → (RelayFresh (relayOf l s′) → ⊥)
                 → DnFresh l s → DnFresh l s′
dnFresh-relayOut l s s′ no fr g′ = ⊥-elim (no g′)

-- NODE D's api SYNC, at the state's slots
dnFresh-nodeDApi : (l : TwoLegs) (s s′ : SysState)
                 → relayOf l s ≡ relayOf l s′
                 → dnCSsOf l s ≡ dnCSsOf l s′
                 → cellCSDn l s ≡ cellCSDn l s′
                 → CliDrvAdj (dnCScC l s) (phOf l s) (dnCScC l s′) (phOf l s′)
                 → DnFresh l s → DnFresh l s′
dnFresh-nodeDApi l s s′ peq seq heq adj =
  dnFresh-lift l s s′ peq
    (λ fr → dnFresh-cliApi _ _ _ _ _ _ adj
              (dnFreshC-cong _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) heq
                             refl refl fr))

-- the SERVER's io FILL, at the state's slots (the cell's two phases come from the
-- medium's banked key lemmas — `PipeMedKey.cell-in-key` returns exactly this pair)
dnFresh-srvSendS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
                 → relayOf l s ≡ relayOf l s′
                 → cellCSDn l s ≡ SM.empty → cellCSDn l s′ ≡ SM.full y
                 → dnCScOf l s ≡ dnCScOf l s′ → phOf l s ≡ phOf l s′
                 → SrvSendAdj (SStep.coarsenCSs (dnCSsOf l s)) y
                              (SStep.coarsenCSs (dnCSsOf l s′))
                 → DnFresh l s → DnFresh l s′
dnFresh-srvSendS l s s′ y peq he he′ keq deq adj =
  dnFresh-lift l s s′ peq
    (λ fr → dnFreshC-cong _ _ _ _ _ _ _ _ refl (sym he′) (cong coarsenCSc keq) deq
              (dnFresh-srvSend _ _ y (dnCScC l s) (phOf l s) adj
                (dnFreshC-cong _ _ _ _ _ _ _ _ refl he refl refl fr)))

-- … the CLIENT's io FILL
dnFresh-cliSendS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
                 → relayOf l s ≡ relayOf l s′
                 → cellCSDn l s ≡ SM.empty → cellCSDn l s′ ≡ SM.full y
                 → dnCSsOf l s ≡ dnCSsOf l s′ → phOf l s ≡ phOf l s′
                 → CliSendAdj (dnCScC l s) y (dnCScC l s′)
                 → DnFresh l s → DnFresh l s′
dnFresh-cliSendS l s s′ y peq he he′ seq deq adj =
  dnFresh-lift l s s′ peq
    (λ fr → dnFreshC-cong _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) (sym he′)
                          refl deq
              (dnFresh-cliSend _ y (dnCScC l s) (dnCScC l s′) (phOf l s) adj
                (dnFreshC-cong _ _ _ _ _ _ _ _ refl he refl refl fr)))

-- … the SERVER's io READ
dnFresh-srvReadS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
                 → relayOf l s ≡ relayOf l s′
                 → cellCSDn l s ≡ SM.full y → cellCSDn l s′ ≡ SM.draining y
                 → dnCScOf l s ≡ dnCScOf l s′ → phOf l s ≡ phOf l s′
                 → SrvReadAdj (SStep.coarsenCSs (dnCSsOf l s)) y
                              (SStep.coarsenCSs (dnCSsOf l s′))
                 → DnFresh l s → DnFresh l s′
dnFresh-srvReadS l s s′ y peq hf he′ keq deq adj =
  dnFresh-lift l s s′ peq
    (λ fr → dnFreshC-cong _ _ _ _ _ _ _ _ refl (sym he′) (cong coarsenCSc keq) deq
              (dnFresh-srvRead _ _ y (dnCScC l s) (phOf l s) adj
                (dnFreshC-cong _ _ _ _ _ _ _ _ refl hf refl refl fr)))

-- … the CLIENT's io READ
dnFresh-cliReadS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
                 → relayOf l s ≡ relayOf l s′
                 → cellCSDn l s ≡ SM.full y → cellCSDn l s′ ≡ SM.draining y
                 → dnCSsOf l s ≡ dnCSsOf l s′ → phOf l s ≡ phOf l s′
                 → CliReadAdj (dnCScC l s) y (dnCScC l s′)
                 → DnFresh l s → DnFresh l s′
dnFresh-cliReadS l s s′ y peq hf he′ seq deq adj =
  dnFresh-lift l s s′ peq
    (λ fr → dnFreshC-cong _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) (sym he′)
                          refl deq
              (dnFresh-cliRead _ y (dnCScC l s) (dnCScC l s′) (phOf l s) adj
                (dnFreshC-cong _ _ _ _ _ _ _ _ refl hf refl refl fr)))

-- … and the medium's DRAIN τ
dnFresh-drainS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
               → relayOf l s ≡ relayOf l s′
               → cellCSDn l s ≡ SM.draining y → cellCSDn l s′ ≡ SM.empty
               → dnCSsOf l s ≡ dnCSsOf l s′
               → dnCScOf l s ≡ dnCScOf l s′ → phOf l s ≡ phOf l s′
               → DnFresh l s → DnFresh l s′
dnFresh-drainS l s s′ y peq hd he′ seq keq deq =
  dnFresh-lift l s s′ peq
    (λ fr → dnFreshC-cong _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) (sym he′)
                          (cong coarsenCSc keq) deq
              (dnFresh-drain _ y (dnCScC l s) (phOf l s)
                (dnFreshC-cong _ _ _ _ _ _ _ _ refl hd refl refl fr)))

------------------------------------------------------------------------
-- §5c  *** NODE D's COUPLING, PRESERVED. ***  `drvCliD-init` and `drvCliD-frame`
-- landed with the object (§1); this is the rest — the api class and the two io
-- classes.
--
-- The section is short for a reason worth recording: the coupling reads exactly two
-- components, its funded clauses are only `cp0` and `cp1`, and *** no api step in
-- `consume` LANDS at `cp0` *** — so the whole api class is `tt`.  *** BUT PRECISELY
-- (the review's M-3): five of the six rows land in `CliAt`'s `⊤` region (`cp2`…`cp6`)
-- and are trivially true, while `cdReq` lands on a FUNDED clause, `CliAt cp1 ccWreq =
-- CliPost ccWreq`.  So the right sentence is "no row lands at `cp0`, and the one row
-- landing at `cp1` lands INSIDE `CliPost`" — not "the class is vacuous"; F59 is the
-- guard that keeps the funded one honest. ***  The io classes are where the region's io-CLOSURE is
-- spent: at `cp0` the client is at `ccIdle`, which has no io row at all
-- (`csCnxt:306-314` are three `apiCS` rows), and at `cp1` `CliPost` is closed under
-- both directions by construction (`ccWreq → ccAwait → {ccArf, ccArb, ccMust} →
-- {ccArf, ccArb}`).
------------------------------------------------------------------------

-- the api class, on EXPLICIT positions (the accessors do not reduce at a variable
-- leg, and a datatype index that is a defined application cannot be matched on)
-- *** THE CASE THIS CLASS COULD NOT BE FED IS FED (T8c-ii). ***  `drvCliD-api` needs a
-- `CliDrvAdj` at the state's slots, and at T8c-0 the cone could not produce one at
-- `(ConsAdv cp0 cp1 , the client's row-fact in its FIXITY arm)`.  §6c's `cliDrvAdj-of`
-- now can, off `LiveLegApiCone` §2b⁵'s sharpening — see the note at `CliDrvAdj`.  *** THE
-- RECORDED CONSEQUENCE STILL HOLDS AND IS WORTH KEEPING: `DnFresh` could be carried
-- across node D's api step WITHOUT the sharpening (`dnFresh-cliApi` covers that case);
-- `DrvCliD` could not. ***  That asymmetry is why the sharpening was on the critical
-- path rather than deferrable — a hypothesis-position datatype left undecided is how C-1
-- happened.
--
-- *** THE `CliAt x ca` HYPOTHESIS IS DISCARDED, and deliberately (the T8b review's
-- M-4). ***  Every row's successor is either in `CliAt`'s `⊤` region or is `cdReq`'s
-- funded `CliPost ccWreq`, so the source's clause is never read.  A successor who
-- WIDENS `CliAt` (funding a third sub-phase, say) must not assume the argument is
-- inert: it is kept in the signature precisely so that widening turns the six `tt`s
-- into real obligations rather than a type error at every call site.
drvCliD-api-at : (ca ca′ : NS.CScPos) (x x′ : ConsPh)
               → CliDrvAdj ca x ca′ x′ → CliAt x ca → CliAt x′ ca′
drvCliD-api-at _ _ _ _ cdReq       _ = tt
drvCliD-api-at _ _ _ _ (cdRecvF _) _ = tt
drvCliD-api-at _ _ _ _ cdDone      _ = tt
drvCliD-api-at _ _ _ _ (cdBF23 _)  _ = tt
drvCliD-api-at _ _ _ _ (cdBF34 _)  _ = tt
drvCliD-api-at _ _ _ _ (cdBF45 _)  _ = tt

-- the io FILL class: the driver's phase is FIXED across an io step, so the clause is
-- read at the SAME sub-phase.  `cp0` refutes all three rows (their sources are not
-- `ccIdle`); at `cp1` the request row carries `CliPost` across and the other two
-- start outside it; `cp2`-`cp6` are `⊤`
drvCliD-send-at : (ca ca′ : NS.CScPos) (y : Payload) (x : ConsPh)
                → CliSendAdj ca y ca′ → CliAt x ca → CliAt x ca′
drvCliD-send-at _ _ _ cp0 csReq    ()
drvCliD-send-at _ _ _ cp0 (csFI _) ()
drvCliD-send-at _ _ _ cp0 csDone   ()
drvCliD-send-at _ _ _ cp1 csReq    _  = tt
drvCliD-send-at _ _ _ cp1 (csFI _) ()
drvCliD-send-at _ _ _ cp1 csDone   ()
drvCliD-send-at _ _ _ cp2 _        _  = tt
drvCliD-send-at _ _ _ cp3 _        _  = tt
drvCliD-send-at _ _ _ cp4 _        _  = tt
drvCliD-send-at _ _ _ cp5 _        _  = tt
drvCliD-send-at _ _ _ cp6 _        _  = tt

-- … the READ twin: `cp0` refutes all seven, `cp1` carries the five whose source is
-- in `CliPost` and refutes the two from `ccInt`
drvCliD-read-at : (ca ca′ : NS.CScPos) (y : Payload) (x : ConsPh)
                → CliReadAdj ca y ca′ → CliAt x ca → CliAt x ca′
drvCliD-read-at _ _ _ cp0 (crRF _ _)  ()
drvCliD-read-at _ _ _ cp0 (crRB _ _)  ()
drvCliD-read-at _ _ _ cp0 crAR        ()
drvCliD-read-at _ _ _ cp0 (crMRF _ _) ()
drvCliD-read-at _ _ _ cp0 (crMRB _ _) ()
drvCliD-read-at _ _ _ cp0 (crIF _ _)  ()
drvCliD-read-at _ _ _ cp0 (crINF _)   ()
drvCliD-read-at _ _ _ cp1 (crRF _ _)  _  = tt
drvCliD-read-at _ _ _ cp1 (crRB _ _)  _  = tt
drvCliD-read-at _ _ _ cp1 crAR        _  = tt
drvCliD-read-at _ _ _ cp1 (crMRF _ _) _  = tt
drvCliD-read-at _ _ _ cp1 (crMRB _ _) _  = tt
drvCliD-read-at _ _ _ cp1 (crIF _ _)  ()
drvCliD-read-at _ _ _ cp1 (crINF _)   ()
drvCliD-read-at _ _ _ cp2 _           _  = tt
drvCliD-read-at _ _ _ cp3 _           _  = tt
drvCliD-read-at _ _ _ cp4 _           _  = tt
drvCliD-read-at _ _ _ cp5 _           _  = tt
drvCliD-read-at _ _ _ cp6 _           _  = tt

------------------------------------------------------------------------
-- §5e  *** THE PRODUCER POSITION — RESOLVED (T8c-0).  Read this before planning any
-- further work on either joint object. ***
--
-- *** VERDICT: BOTH PRODUCERS EXIST AND ARE GREEN. ***  This section recorded a BLOCKED
-- verdict in the T8b fix round; `0db5458` unblocked it, and what follows is the resolved
-- history, kept because the four negative results are permanent facts about the cone's
-- own objects and a successor will otherwise re-attempt the routes they close.
--
-- *** THE FOUR NEGATIVES (machine-checked, probe `ProbeT8bFx`, run then deleted). ***
--   (A1) `RelayAdv` is NOT producible from `RelayStepKind` — the relay-phase fact
--        `PipeEvDriverCone.LegDriverStep.ldRelay` exposes.  Witness: `RelayStepKind
--        (producing b pp1) (producing b pp0)` is INHABITED (`RelayHas` is `⊤` at both,
--        `RelayPre`/`RelayFwd` `⊥` at both) while `RelayAdv` there is EMPTY.  *** AND NO
--        GUARD CAN FIX IT: *** any region that is `RelayStepKind`-backward-closed must
--        contain `pp1` whenever it contains `pp0`, and the arms need `pp0` IN and the
--        emit's successor `pp1` OUT.  The region is right; the classifier is too coarse.
--   (A2) nor from `LiveLegApiCone.DnCsDrv` (`:3285-3286`), whose landing arm is two
--        conditionals keyed on the SUCCESSOR phase and is therefore inhabited VACUOUSLY
--        wherever the successor is neither `pp1` nor `pp2` — including at a pair that is
--        no advance at all.
--   (B1) `CliDrvAdj` is NOT producible from `ConsAdv` + the client row's FIXITY arm:
--        `ConsAdv cp0 cp1` with the client fixed satisfies both ingredients, and
--        `CliDrvAdj ccIdle cp0 ccIdle cp1` is EMPTY.
--   (B2) nor from `ConsAdv` + a GENUINE client row: `ConsAdv cp1 cp2` with `caReq` is
--        §5's own "individually consistent, jointly impossible" pair.
--
-- *** WHAT RESOLVED IT (T8c-0), and it was not what this section predicted. ***  The
-- shared cause was right — both objects are LANDING-class facts determined by the firing
-- driver's STEP, which the cone binds at its four `dStep` sites (`LiveLegApiCone:2915`,
-- `:2994`, `:3126`, `:3196`) and at node D's two, while every field of `DriverExposed⁺`,
-- `NodeBApiEvo`, `LegDriverStep` and `VisLeaves⁺` was an already-APPLIED consequence.  The
-- fix was one field per axis:
--   · the RELAY axis: `RelayAdv` moved INTO the cone and the extraction became
--     `cpStepKindQ-of⁺`'s EIGHTEENTH component — not a standalone `relayAdv-of` lemma,
--     which this section used to name and which no longer exists.  *** That is the only
--     shape that typechecks: *** two independent dispatches on the same phase give equal
--     `x′` TERMS, but a `with`-abstracted consumer cannot see it, so the component route
--     is what keeps `x′` single-sourced with the arm's own `cp-B nb′`.  Carried out as
--     `DriverExposed⁺.deRelayAdvBD`/`-CD`; selected per leg by `relayAdv-leg`, which is
--     pure selection because `relayOf legBD s` IS `cp-B (nB s)` — no bridge lemma owed.
--   · NODE D's axis: no new cone work at all.  `NodeDApiEvo`'s two constructors have
--     carried the driver STEP since grant #5, and only the threading was absent
--     (`deConsStepBD`/`-CD`).  *** BANK THAT: before pricing a cone edit, check whether
--     the ARM RECORD already carries the datum and only `DriverExposed⁺` lacks it. ***
--
-- *** TWO PREDICTIONS THIS SECTION GOT WRONG, corrected here rather than quietly. ***
--   (i) "THE FIX IS ONE FIELD, NOT A DESIGN … it deserves its own task, sequenced as
--       T6c/T7 were" — the field count was right, the task sizing was not: the whole
--       threading measured 28 net.
--  (ii) "the ~360s-rebuild class" — MEASURED WRONG BY 6×.  The endpoint rebuild after the
--       threading was *** 11 modules, ~60s ***, because the change is purely ADDITIVE (a
--       Σ tail and four record fields).  *** The ~360s figure is for a cone edit that
--       CHANGES an existing type; an additive one is ~60s. ***  And the standing advice
--       "DO NOT IMPROVISE A LEAF-LOCAL SUBSTITUTE" survives A1 unchanged — there is no
--       leaf-local substitute for the relay axis — but it is no longer a reason to defer.
--
-- *** THE ONE RESIDUAL WAS A SHARPENING rather than a threading, AND IT IS LANDED
-- (T8c-ii). ***  See the notes at `CliDrvAdj` and at `drvCliD-api-at`: `CliDrvAdj` was
-- producible except at `(ConsAdv cp0 cp1 , the CS client's row-fact in its FIXITY arm)`,
-- and what closed it is `LiveLegApiCone` §2b⁵ — the bundle now reports the client's fact
-- as the ROW arm at an `apiCS` label on the client's own key, refuted in the
-- server-fired arm by `cl ≢ sv`.  §6c's `cliDrvAdj-of` is the producer, total on the
-- driver's six hops, and it needs NO new cone field beyond that one component: the
-- determining data are the driver's own step (already threaded as `deConsStep*`) and the
-- client's api fact (already threaded as `deCSDnCli*`).  *** SO §5e's whole subject is
-- now closed: both joint objects have machine-checked producers at the shapes their
-- consumers call them with. ***

-- the api class, at the state's two slots
drvCliD-api : (l : TwoLegs) (s s′ : SysState)
            → CliDrvAdj (dnCScC l s) (phOf l s) (dnCScC l s′) (phOf l s′)
            → DrvCliD l s → DrvCliD l s′
drvCliD-api l s s′ adj g x eq =
  subst (λ z → CliAt z (dnCScC l s′)) eq
    (drvCliD-api-at (dnCScC l s) (dnCScC l s′) (phOf l s) (phOf l s′) adj
      (g (phOf l s) refl))

-- … the io FILL class
drvCliD-send : (l : TwoLegs) (s s′ : SysState) (y : Payload)
             → phOf l s ≡ phOf l s′
             → CliSendAdj (dnCScC l s) y (dnCScC l s′)
             → DrvCliD l s → DrvCliD l s′
drvCliD-send l s s′ y deq adj g x eq =
  drvCliD-send-at (dnCScC l s) (dnCScC l s′) y x adj (g x (trans deq eq))

-- … and the io READ class
drvCliD-read : (l : TwoLegs) (s s′ : SysState) (y : Payload)
             → phOf l s ≡ phOf l s′
             → CliReadAdj (dnCScC l s) y (dnCScC l s′)
             → DrvCliD l s → DrvCliD l s′
drvCliD-read l s s′ y deq adj g x eq =
  drvCliD-read-at (dnCScC l s) (dnCScC l s′) y x adj (g x (trans deq eq))

------------------------------------------------------------------------
-- §6  *** THE UNOFFERED-LABEL FAMILY — THE FIRST LEMMA OF THIS SHAPE IN THE
-- TREE. ***
--
-- What it proves, and what depends on it: node D's consume driver NEVER offers
-- `apiCS l hi sendCSFindIntersect`, at any phase, and does not offer `apiCS l hi
-- sendCSDone` at either FRESH phase.  Those two facts are (a) the completeness
-- argument for §5's `CliDrvAdj` — they are why there is no seventh row and no
-- `cdDone` at `cp0`/`cp1` — and (b) the only support for TWO of `CliFresh`'s nine
-- exclusions, `ccWfi` and `ccWdone` (the client's `ccIdle` exits at
-- `csCnxt:309-314`).  Every other exclusion rests on the cell conjunct.
--
-- *** NO LEMMA OF THIS SHAPE EXISTED — grepped, not relayed. ***  The driver
-- no-offer family in the tree is keyed by event CLASS (`SysOracle:2046`, `¬
-- IsApiCSBF e → ¬ IoOffers (decConsD l cph) e a`) or by LINK (`SysRoute:306`,
-- `:312`), never by LABEL; the nearest SHAPE is the peer-side per-label dispatch of
-- `SysIoLink5` (`:1107-1281`).  This section is the label-level DRIVER refusal, and
-- it is built the way the class-level ones are, one clause per phase.
--
-- *** WHY IT IS `viewV … ≡ nothing` AND NOT A STEP INVERSION. ***  The banked
-- class-level lemmas inverting a step (`bind-ev-inv` then `⟶₀-ev-inv`) recover the
-- fired event's LABEL as an equation and then read a classifier off it.  That route
-- is unavailable at a CONCRETE label: the label equation would have to unify two
-- concrete carrier SETS (`ApiCSCar sendCSFindIntersect` against `ApiCSCar
-- sendCSRequestNext`, i.e. `List Point` against `⊤`), and Agda cannot refute an
-- equation between `Set`s by pattern matching.  So the family goes the other way —
-- COMPUTE the visible map at the concrete event and get `nothing` — which needs no
-- unification at all.  `≟-yes-refl` is needed for `consVis-cp0`'s reason
-- (`Net_Api-≟` tests the LINK first, `Net:1105`, and the link is a variable); once
-- that is discharged the api TAG comparison decides `no` by computation and each
-- clause is a `refl`.  The `>> Skip` bind is crossed by computation too, not by
-- inversion: at a `react` head the bind's own visible map is the inner one mapped,
-- so `nothing` propagates.
------------------------------------------------------------------------

-- *** THE BRIDGE: a tree whose visible map is `nothing` at `(e , a)` OFFERS nothing
-- there. ***  The converse of `SysOracle_GapBDisj.noOffer→viewV`, which the tree has
-- only in the direction that DISCARDS the offer.  Every member of this section
-- crosses it
viewV-no : (P : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
         → viewV (PTree.force P) (X , e) a ≡ nothing
         → IoOffers P e a → ⊥
viewV-no P {X} {e} {a} veq (M , sVis fEq vEq) =
  nothing-absurd
    (trans (sym (subst (λ z → viewV z (X , e) a ≡ nothing) fEq veq)) vEq)

-- node D's consume driver offers NO `sendCSFindIntersect`, at ANY of its seven
-- phases.  Six clauses compute the visible map of a concrete prefix/output head
-- against the wrong api tag; the seventh (`cp6`) is `Ret b >> Skip`, whose forced
-- node is not a `react` at all, so its map is `∅v` and no rewrite is needed
consDVis-no-fi : (l : Link) (b : Block₃) (x : ConsPh)
                 (ps : ApiCSCar sendCSFindIntersect)
               → viewV (PTree.force (decConsD l (consD b x)))
                       (_ , apiCS l hi sendCSFindIntersect) ps ≡ nothing
-- *** THE REWRITE IS NEEDED AT EXACTLY THE `apiCS` HEADS, and measured so: at
-- `cp2`/`cp3`/`cp4` the head is an `apiBF` event, so `Net_Api-≟` decides `no` on the
-- CROSS-CONSTRUCTOR clause (`Net:1147+`) without ever reaching the link test, and
-- putting a `rewrite` there is a `-WRewritesNothing` warning rather than a
-- no-op. ***
consDVis-no-fi l b cp0 ps rewrite ≟-yes-refl l = refl
consDVis-no-fi l b cp1 ps rewrite ≟-yes-refl l = refl
consDVis-no-fi l b cp2 ps = refl
consDVis-no-fi l b cp3 ps = refl
consDVis-no-fi l b cp4 ps = refl
consDVis-no-fi l b cp5 ps rewrite ≟-yes-refl l = refl
consDVis-no-fi l b cp6 ps = refl

-- *** …hence the refusal, which is what a `CliDrvAdj` producer consumes: the
-- client's `ccIdle → ccWfi ps` row can never fire, because its `apiES` partner does
-- not exist. ***  Phase-GENERIC — the label is absent from `consume` altogether
consD-no-fi : (l : Link) (b : Block₃) (x : ConsPh)
              (ps : ApiCSCar sendCSFindIntersect)
            → IoOffers (decConsD l (consD b x)) (apiCS l hi sendCSFindIntersect) ps
            → ⊥
consD-no-fi l b x ps =
  viewV-no (decConsD l (consD b x)) (consDVis-no-fi l b x ps)

-- … and the `sendCSDone` half, which is phase-SCOPED rather than absent: the label
-- IS in `consume`, at `cp5` (`SysNode:955-957`), so the refusal is exactly as wide
-- as `PhFresh` — which is all §4's client half needs, `ccWdone`'s exclusion being
-- scoped by the phase conjunct.  The five non-fresh phases are refuted by the
-- conjunct itself and never compute a map
consDVis-no-done : (l : Link) (b : Block₃) (x : ConsPh) → PhFresh x
                 → viewV (PTree.force (decConsD l (consD b x)))
                         (_ , apiCS l hi sendCSDone) U.tt ≡ nothing
consDVis-no-done l b cp0 _  rewrite ≟-yes-refl l = refl
consDVis-no-done l b cp1 _  rewrite ≟-yes-refl l = refl
consDVis-no-done l b cp2 ()
consDVis-no-done l b cp3 ()
consDVis-no-done l b cp4 ()
consDVis-no-done l b cp5 ()
consDVis-no-done l b cp6 ()

-- *** …hence the second refusal: inside the fresh phase region the client's `ccIdle
-- → ccWdone` row can never fire either. ***
consD-no-done : (l : Link) (b : Block₃) (x : ConsPh) → PhFresh x
              → IoOffers (decConsD l (consD b x)) (apiCS l hi sendCSDone) U.tt → ⊥
consD-no-done l b x hp =
  viewV-no (decConsD l (consD b x)) (consDVis-no-done l b x hp)

------------------------------------------------------------------------
-- §6b  *** (T8b FIX ROUND) THE FAMILY COMPLETED — the POSITIVE complement, and the
-- three remaining CLIENT labels. ***  (the fix round's I-1)
--
-- §6 as first shipped says which labels node D's driver NEVER offers.  Two more
-- things are owed, and both are this same computation:
--
--   (1) THE POSITIVE COMPLEMENT.  For a label the driver DOES offer, a `CliDrvAdj`
--       producer needs that it offers it at ONE phase only — otherwise the joint
--       adjacency's phase pair is not determined by the label.  Two members, one per
--       CS chain event that moves the client (`sendCSRequestNext` at `cp0`,
--       `recvCSRollforward` at `cp1`), each stated as "not offered ANYWHERE ELSE" so
--       that the offering phase is excluded by the caller's own premise.
--   (2) THE THREE REMAINING CLIENT LABELS.  `CliDrvAdj` omits four of
--       `LiveChanCS.CliApiAdj`'s seven rows (see the note at the datatype), and the
--       justification for three of them — `caRecvB`, `caRecvIF`, `caRecvIN` — is that
--       their labels are absent from `consume` entirely, exactly as
--       `sendCSFindIntersect` is.  Those three refusals are built here so the
--       omission set is FULLY machine-checked rather than three-quarters argued.
--
-- Together with §6's two members this is every CS label a client row can carry —
-- `csCnxt`'s seven api rows use *** SEVEN *** distinct tags (`sendCSRequestNext`,
-- `sendCSFindIntersect`, `sendCSDone`, `recvCSRollforward`, `recvCSRollback`,
-- `recvCSIntersectFound`, `recvCSIntersectNotFound`), and §6+§6b cover all seven — so
-- the omission set of `CliDrvAdj` is closed over the WHOLE table, not over a subset.
------------------------------------------------------------------------

-- (1a) `sendCSRequestNext` is offered at `cp0` and NOWHERE else
consDVis-req-off : (l : Link) (b : Block₃) (x : ConsPh) → (x ≡ cp0 → ⊥)
                 → viewV (PTree.force (decConsD l (consD b x)))
                         (_ , apiCS l hi sendCSRequestNext) U.tt ≡ nothing
consDVis-req-off l b cp0 no = ⊥-elim (no refl)
consDVis-req-off l b cp1 _  rewrite ≟-yes-refl l = refl
consDVis-req-off l b cp2 _  = refl
consDVis-req-off l b cp3 _  = refl
consDVis-req-off l b cp4 _  = refl
consDVis-req-off l b cp5 _  rewrite ≟-yes-refl l = refl
consDVis-req-off l b cp6 _  = refl

consD-req-off : (l : Link) (b : Block₃) (x : ConsPh) → (x ≡ cp0 → ⊥)
              → IoOffers (decConsD l (consD b x)) (apiCS l hi sendCSRequestNext) U.tt
              → ⊥
consD-req-off l b x no =
  viewV-no (decConsD l (consD b x)) (consDVis-req-off l b x no)

-- (1b) … and `recvCSRollforward` at `cp1` and nowhere else
consDVis-rf-off : (l : Link) (b : Block₃) (x : ConsPh)
                  (ht : ApiCSCar recvCSRollforward) → (x ≡ cp1 → ⊥)
                → viewV (PTree.force (decConsD l (consD b x)))
                        (_ , apiCS l hi recvCSRollforward) ht ≡ nothing
consDVis-rf-off l b cp0 ht _  rewrite ≟-yes-refl l = refl
consDVis-rf-off l b cp1 ht no = ⊥-elim (no refl)
consDVis-rf-off l b cp2 ht _  = refl
consDVis-rf-off l b cp3 ht _  = refl
consDVis-rf-off l b cp4 ht _  = refl
consDVis-rf-off l b cp5 ht _  rewrite ≟-yes-refl l = refl
consDVis-rf-off l b cp6 ht _  = refl

consD-rf-off : (l : Link) (b : Block₃) (x : ConsPh)
               (ht : ApiCSCar recvCSRollforward) → (x ≡ cp1 → ⊥)
             → IoOffers (decConsD l (consD b x)) (apiCS l hi recvCSRollforward) ht → ⊥
consD-rf-off l b x ht no =
  viewV-no (decConsD l (consD b x)) (consDVis-rf-off l b x ht no)

-- (2a) `recvCSRollback` — never offered, at any phase.  This is what justifies
-- `CliDrvAdj`'s omission of `caRecvB`
consDVis-no-rb : (l : Link) (b : Block₃) (x : ConsPh)
                 (pt : ApiCSCar recvCSRollback)
               → viewV (PTree.force (decConsD l (consD b x)))
                       (_ , apiCS l hi recvCSRollback) pt ≡ nothing
consDVis-no-rb l b cp0 pt rewrite ≟-yes-refl l = refl
consDVis-no-rb l b cp1 pt rewrite ≟-yes-refl l = refl
consDVis-no-rb l b cp2 pt = refl
consDVis-no-rb l b cp3 pt = refl
consDVis-no-rb l b cp4 pt = refl
consDVis-no-rb l b cp5 pt rewrite ≟-yes-refl l = refl
consDVis-no-rb l b cp6 pt = refl

consD-no-rb : (l : Link) (b : Block₃) (x : ConsPh) (pt : ApiCSCar recvCSRollback)
            → IoOffers (decConsD l (consD b x)) (apiCS l hi recvCSRollback) pt → ⊥
consD-no-rb l b x pt =
  viewV-no (decConsD l (consD b x)) (consDVis-no-rb l b x pt)

-- (2b) `recvCSIntersectFound` — never offered (justifies omitting `caRecvIF`)
consDVis-no-if : (l : Link) (b : Block₃) (x : ConsPh)
                 (pt : ApiCSCar recvCSIntersectFound)
               → viewV (PTree.force (decConsD l (consD b x)))
                       (_ , apiCS l hi recvCSIntersectFound) pt ≡ nothing
consDVis-no-if l b cp0 pt rewrite ≟-yes-refl l = refl
consDVis-no-if l b cp1 pt rewrite ≟-yes-refl l = refl
consDVis-no-if l b cp2 pt = refl
consDVis-no-if l b cp3 pt = refl
consDVis-no-if l b cp4 pt = refl
consDVis-no-if l b cp5 pt rewrite ≟-yes-refl l = refl
consDVis-no-if l b cp6 pt = refl

consD-no-if : (l : Link) (b : Block₃) (x : ConsPh)
              (pt : ApiCSCar recvCSIntersectFound)
            → IoOffers (decConsD l (consD b x)) (apiCS l hi recvCSIntersectFound) pt
            → ⊥
consD-no-if l b x pt =
  viewV-no (decConsD l (consD b x)) (consDVis-no-if l b x pt)

-- (2c) `recvCSIntersectNotFound` — never offered (justifies omitting `caRecvIN`)
consDVis-no-in : (l : Link) (b : Block₃) (x : ConsPh)
                 (tp : ApiCSCar recvCSIntersectNotFound)
               → viewV (PTree.force (decConsD l (consD b x)))
                       (_ , apiCS l hi recvCSIntersectNotFound) tp ≡ nothing
consDVis-no-in l b cp0 tp rewrite ≟-yes-refl l = refl
consDVis-no-in l b cp1 tp rewrite ≟-yes-refl l = refl
consDVis-no-in l b cp2 tp = refl
consDVis-no-in l b cp3 tp = refl
consDVis-no-in l b cp4 tp = refl
consDVis-no-in l b cp5 tp rewrite ≟-yes-refl l = refl
consDVis-no-in l b cp6 tp = refl

consD-no-in : (l : Link) (b : Block₃) (x : ConsPh)
              (tp : ApiCSCar recvCSIntersectNotFound)
            → IoOffers (decConsD l (consD b x)) (apiCS l hi recvCSIntersectNotFound) tp
            → ⊥
consD-no-in l b x tp =
  viewV-no (decConsD l (consD b x)) (consDVis-no-in l b x tp)

------------------------------------------------------------------------
-- §6d  *** (T9) THE FAMILY's FIRST BLOCKFETCH MEMBER — the positive complement
-- for `sendBFRequestRange`. ***
--
-- WHY IT IS HERE AND NOT IN A BF-NAMED FILE.  It is §6b(1)'s shape at the ONE
-- BlockFetch label a client row can carry on node D's side, and it needs
-- `viewV-no`, `≟-yes-refl` and `decConsD` — the three things this section already
-- has.  A separate file would duplicate all three for ten lines.
--
-- WHAT IT IS FOR, and this is the load-bearing part: it is the fact that decides
-- the `pp3` arm's shape.  `LiveRelayCS` §5b's inventory needs to know at WHICH
-- phases node D's driver offers the BlockFetch request, because that is what says
-- which sub-cases of `bcIdle` have a node-internal api sync to be refuted by and
-- which do not.  The answer is `cp2` and `cp2` ONLY — so `cp0` is refutable off
-- the LANDED `cliIdle-cp0-⊥` (the driver's CS head) and `cp1` has NO
-- BlockFetch-hop refutation at all.  See `LiveRelayCS` §5b.
--
-- THE REWRITE PATTERN IS THE MIRROR IMAGE of §6/§6b's.  There the target was an
-- `apiCS` label and the rewrite was needed at the `apiCS` heads (`cp0`/`cp1`/`cp5`);
-- here the target is an `apiBF` label, so `Net_Api-≟` reaches the LINK test only at
-- the `apiBF` heads and the rewrite is needed at `cp3`/`cp4` — `cp2` being the
-- offering phase and therefore an absurd clause.  At `cp0`/`cp1`/`cp5` the decision
-- is CROSS-CONSTRUCTOR and never reaches the link, and `cp6` (`Ret b >> Skip`)
-- forces to a node that is not a `react` at all.
------------------------------------------------------------------------

-- `sendBFRequestRange` is offered at `cp2` and NOWHERE else
consDVis-brr-off : (l : Link) (b : Block₃) (x : ConsPh)
                   (rg : ApiBFCar sendBFRequestRange) → (x ≡ cp2 → ⊥)
                 → viewV (PTree.force (decConsD l (consD b x)))
                         (_ , apiBF l hi sendBFRequestRange) rg ≡ nothing
consDVis-brr-off l b cp0 rg _  = refl
consDVis-brr-off l b cp1 rg _  = refl
consDVis-brr-off l b cp2 rg no = ⊥-elim (no refl)
consDVis-brr-off l b cp3 rg _  rewrite ≟-yes-refl l = refl
consDVis-brr-off l b cp4 rg _  rewrite ≟-yes-refl l = refl
consDVis-brr-off l b cp5 rg _  = refl
consDVis-brr-off l b cp6 rg _  = refl

-- … hence the refusal: outside `cp2` the BF client's `bcIdle → bcWrr rg` row
-- (`NodeSpecs:518-521`) can never fire, because its `apiES` partner does not exist
consD-brr-off : (l : Link) (b : Block₃) (x : ConsPh)
                (rg : ApiBFCar sendBFRequestRange) → (x ≡ cp2 → ⊥)
              → IoOffers (decConsD l (consD b x)) (apiBF l hi sendBFRequestRange) rg
              → ⊥
consD-brr-off l b x rg no =
  viewV-no (decConsD l (consD b x)) (consDVis-brr-off l b x rg no)

-- *** THE SPECIALISATION `LiveRelayCS` §5b's INVENTORY TURNS ON: at `cp1` node D's
-- driver offers the BlockFetch request NOT AT ALL. ***  So the `(bsIdle , empty ,
-- bcIdle)` configuration with node D's driver at `cp1` has no node-internal api sync
-- on the BlockFetch hop to be refuted by — unlike `cp2`, where the sync is the whole
-- refutation, and unlike `cp0`, where §3's `cliIdle-cp0-⊥` refutes on the ChainSync
-- hop instead.  Stated as its own name because it is a NEGATIVE result being cited
-- from another file, and a citation of the general form would leave the reader to
-- re-derive `cp1 ≢ cp2`
consD-cp1-no-brr : (l : Link) (b : Block₃) (rg : ApiBFCar sendBFRequestRange)
                 → IoOffers (decConsD l (consD b cp1)) (apiBF l hi sendBFRequestRange) rg
                 → ⊥
consD-cp1-no-brr l b rg = consD-brr-off l b cp1 rg (λ ())

------------------------------------------------------------------------
-- §6e  (T11) *** THE FAMILY's SECOND BLOCKFETCH MEMBER, AND THE `cp2` api SYNC
-- — the two halves of `LiveDrvBFD.bfFresh⇒areq`'s fourth premise and of T9's
-- half-checked claim. ***
--
-- (a) THE MEMBER.  T9 §5b's inventory says of the `(pp3 , cp1)` leaf that
-- "`bcIdle`'s two rows are both api and node D's driver offers NEITHER of them at
-- `cp1`".  §6d machine-checked the FIRST row's label (`sendBFRequestRange`, at
-- `cp2` and nowhere else); the second (`sendBFClientDone`) had no member anywhere
-- in the tree, so the claim was HALF checked — the T9 verification's first
-- inventory gap.  `consDVis-bcd-off` closes it: the label is offered at `cp4` and
-- nowhere else, so at `cp1` neither of the client's two api rows has an `apiES`
-- partner.  The rewrite sites move with the offering phase, exactly as §6d's note
-- predicts: the `apiBF` heads are `cp2` and `cp3` here (where §6d's were `cp3`
-- and `cp4`), and `cp4` is the absurd clause.
--
-- (b) THE SYNC.  §3's `cliIdle-cp0-⊥` one PROTOCOL over: at `cp2` node D's driver
-- fires `sendBFRequestRange` and its own BF client at `bcIdle` accepts it, so a
-- stable configuration cannot sit there.  TWO differences from §3, both of them
-- in the rung-1 lemma and neither in the kit: the driver's prefix is an OUTPUT
-- (`decCons … cp2` pins the value `chainRange (point b) (point b)`), so the value
-- test needs unsticking beside the link test — `LiveRelayOpen.prodVis-pp2`'s own
-- idiom; and the peer's row accepts EVERY range (`ceqBFc01`), so the sync fires
-- at the driver's own pin with no value gate on the client side.  §2's two sync
-- kits are reused verbatim: an api sync inside node D is an api sync inside node
-- D whichever protocol's event it carries.
------------------------------------------------------------------------

-- (a) `sendBFClientDone` is offered at `cp4` and NOWHERE else
consDVis-bcd-off : (l : Link) (b : Block₃) (x : ConsPh)
                   (a : ApiBFCar sendBFClientDone) → (x ≡ cp4 → ⊥)
                 → viewV (PTree.force (decConsD l (consD b x)))
                         (_ , apiBF l hi sendBFClientDone) a ≡ nothing
consDVis-bcd-off l b cp0 a _  = refl
consDVis-bcd-off l b cp1 a _  = refl
consDVis-bcd-off l b cp2 a _  rewrite ≟-yes-refl l = refl
consDVis-bcd-off l b cp3 a _  rewrite ≟-yes-refl l = refl
consDVis-bcd-off l b cp4 a no = ⊥-elim (no refl)
consDVis-bcd-off l b cp5 a _  = refl
consDVis-bcd-off l b cp6 a _  = refl

-- … hence the refusal: outside `cp4` the BF client's `bcIdle → bcWcd` row
-- (`NodeSpecs:522-524`) can never fire, because its `apiES` partner does not exist
consD-bcd-off : (l : Link) (b : Block₃) (x : ConsPh)
                (a : ApiBFCar sendBFClientDone) → (x ≡ cp4 → ⊥)
              → IoOffers (decConsD l (consD b x)) (apiBF l hi sendBFClientDone) a
              → ⊥
consD-bcd-off l b x a no =
  viewV-no (decConsD l (consD b x)) (consDVis-bcd-off l b x a no)

-- *** THE SPECIALISATION THAT COMPLETES T9's CLAIM: at `cp1` node D's driver
-- offers the client-done NOT AT ALL EITHER. ***  With §6d's `consD-cp1-no-brr`
-- this is the whole of "`bcIdle`'s two rows are both api and neither has a partner
-- at `cp1`" — the sentence `LiveRelayCS` §5b states and, until now, half proved
consD-cp1-no-bcd : (l : Link) (b : Block₃) (a : ApiBFCar sendBFClientDone)
                 → IoOffers (decConsD l (consD b cp1)) (apiBF l hi sendBFClientDone) a
                 → ⊥
consD-cp1-no-bcd l b a = consD-bcd-off l b cp1 a (λ ())

-- (b) node D's consume driver at `cp2` fires the range request — an OUTPUT
-- prefix, so the value test is unstuck beside the link test
consVis-cp2 : (l : Link) (b₀ : Block₃)
  → viewV (PTree.force (decCons l hi b₀ cp2))
          (ChainRange , apiBF l hi sendBFRequestRange)
          (chainRange (point b₀) (point b₀))
    ≡ just (decCons l hi b₀ cp3)
consVis-cp2 l b₀ rewrite ≟-yes-refl l
  | ≟-yes-refl (chainRange (point b₀) (point b₀)) = refl

-- … and so the whole `consume l hi >> Skip` driver does (§3's `consD-offer-req`
-- at the other phase)
consD-offer-brr : (l : Link) (b₀ : Block₃)
  → IoOffers (decConsD l (consD b₀ cp2)) (apiBF l hi sendBFRequestRange)
             (chainRange (point b₀) (point b₀))
consD-offer-brr l b₀ =
    _
  , TLB.bind-ev (λ _ → Skip) (decCons l hi b₀ cp2) (sVis refl (consVis-cp2 l b₀))

-- the BF CLIENT at a position coarsening to `bcIdle` offers `sendBFRequestRange`
-- at EVERY range (`bfCnxt bcIdle`, `NodeSpecs:518-521`; the row is `ceqBFc01`).
-- §3's `peer-cD0` on the other axis
peer-bD2 : (i : Link) (d : Dir) (q : SN.BFcPos) (rg : ChainRange)
         → coarsenBFc q ≡ NS.bcIdle
         → absBFc i d q
             ─[ ev (evl (evLabel ChainRange (apiBF i d sendBFRequestRange) rg)) ]─►
           absBFc i d (SN.bcReq1 rg)
peer-bD2 i d q rg pin =
  aBFc i d q (SN.bcReq1 rg)
    (subst (λ z → NS.bfCfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfCnxt i d z (ChainRange , apiBF i d sendBFRequestRange) rg
                  ≡ just (NS.bcWrr rg))
           (sym pin) (ceqBFc01 {rg} i d))

-- *** THE REFUTATION `bfFresh⇒areq`'s FOURTH PREMISE CONSUMES, leg BD. ***  a
-- STABLE configuration cannot have node D's dn BF client at `bcIdle` while node
-- D's own consume driver is at `cp2`: the client accepts the driver's pinned
-- request, the sync is node-internal, and the event is hidden by `keptB`'s
-- catch-all (`Spec:109-115` keeps only `sendBFBlock`/`recvBFBlock`/`break`)
bfIdle-cp2-BD-⊥ : (r : RState) (b₀ : Block₃)
  → coarsenBFc (SN.NodeStateD.bfC-BD (nD (toSys r))) ≡ NS.bcIdle
  → SN.NodeStateD.cons-BD (nD (toSys r)) ≡ consD b₀ cp2
  → isStable (radec r ∖ hidden blkA) → ⊥
bfIdle-cp2-BD-⊥ r b₀ pin hcons sta =
  syncD-BD r aicBF ahlBF aicBFreq refl (λ ()) tt
    (absBundle-BFc-ev linkBD hi lo
       (SN.NodeStateD.csC-BD (nD (toSys r))) (SN.NodeStateD.csS-BD (nD (toSys r)))
       (SN.NodeStateD.bfC-BD (nD (toSys r))) (SN.NodeStateD.bfS-BD (nD (toSys r)))
       (SN.NodeStateD.inert-BD (nD (toSys r)))
       {e₁ = BF.apiBFev linkBD hi sendBFRequestRange}
       {qbc′ = SN.bcReq1 (chainRange (point b₀) (point b₀))} (λ ()) refl
       (peer-bD2 linkBD hi (SN.NodeStateD.bfC-BD (nD (toSys r)))
                 (chainRange (point b₀) (point b₀)) pin))
    (subst (λ q → IoOffers (decConsD linkBD q) (apiBF linkBD hi sendBFRequestRange)
                           (chainRange (point b₀) (point b₀)))
           (sym hcons) (consD-offer-brr linkBD b₀))
    sta

-- … the CD-leg mirror
bfIdle-cp2-CD-⊥ : (r : RState) (b₀ : Block₃)
  → coarsenBFc (SN.NodeStateD.bfC-CD (nD (toSys r))) ≡ NS.bcIdle
  → SN.NodeStateD.cons-CD (nD (toSys r)) ≡ consD b₀ cp2
  → isStable (radec r ∖ hidden blkA) → ⊥
bfIdle-cp2-CD-⊥ r b₀ pin hcons sta =
  syncD-CD r aicBF ahlBF aicBFreq refl (λ ()) tt
    (absBundle-BFc-ev linkCD hi lo
       (SN.NodeStateD.csC-CD (nD (toSys r))) (SN.NodeStateD.csS-CD (nD (toSys r)))
       (SN.NodeStateD.bfC-CD (nD (toSys r))) (SN.NodeStateD.bfS-CD (nD (toSys r)))
       (SN.NodeStateD.inert-CD (nD (toSys r)))
       {e₁ = BF.apiBFev linkCD hi sendBFRequestRange}
       {qbc′ = SN.bcReq1 (chainRange (point b₀) (point b₀))} (λ ()) refl
       (peer-bD2 linkCD hi (SN.NodeStateD.bfC-CD (nD (toSys r)))
                 (chainRange (point b₀) (point b₀)) pin))
    (subst (λ q → IoOffers (decConsD linkCD q) (apiBF linkCD hi sendBFRequestRange)
                           (chainRange (point b₀) (point b₀)))
           (sym hcons) (consD-offer-brr linkCD b₀))
    sta

-- *** THE LEG-DISPATCHED FORM — what `LiveRelayCS` §2d consumes. ***  §3's
-- `cliIdle-cp0-⊥` shape: the dispatch is on an EXPLICIT `TwoLegs` argument and
-- never a `with`, because at a variable leg the accessors do not reduce
bfIdle-cp2-⊥ : (l : TwoLegs) (r : RState) (b₀ : Block₃)
  → coarsenBFc (dnClient l (toSys r)) ≡ NS.bcIdle
  → phOf l (toSys r) ≡ cp2
  → cblkOf l (toSys r) ≡ b₀
  → isStable (radec r ∖ hidden blkA) → ⊥
bfIdle-cp2-⊥ legBD r b₀ pin hph hbk =
  bfIdle-cp2-BD-⊥ r b₀ pin (consD-η (SN.NodeStateD.cons-BD (nD (toSys r))) hph hbk)
bfIdle-cp2-⊥ legCD r b₀ pin hph hbk =
  bfIdle-cp2-CD-⊥ r b₀ pin (consD-η (SN.NodeStateD.cons-CD (nD (toSys r))) hph hbk)

------------------------------------------------------------------------
-- §6f  (T11) *** THE `cp1` api SYNC — ONE OF THE LEAF's FIVE POSITIONS,
-- DISCHARGED, and the four that remain, machine-checked. ***
--
-- T9's `cp1` leaf (`LiveRelayCS` §5b) is the `(pp3 , cp1)` configuration whose
-- refutation must come off the CHAINSYNC axis, and its inventory item (iv) is
-- "the node-D api sync at `cp1` for the `ccArf ht` member — the `cliIdle-cp0-⊥`
-- transposition, with the `Header × Tip` value gate; THIS ONE IS CHEAP".  It is,
-- and §6e's `cp2` twin is why: the sync KITS (§2) are protocol- and
-- phase-generic, so a new member costs its rung 1 and nothing else.
--
-- TWO differences from §6e's, both in rung 1 and both the mirror of it: the
-- driver's prefix at `cp1` is an INPUT (`decCons … cp1 = apiCS l d
-- recvCSRollforward ⟶ consume-k l d`), so the driver accepts EVERY value and its
-- own continuation is a FUNCTION of it — which is why `consVis-cp1` returns the
-- successor existentially rather than naming it (naming it would import
-- `consume-k` for one line); and the PEER's row is the value-GATED one
-- (`csCnxt (ccArf (h , t)) … recvCSRollforward (h , t)`, `ceqCSc15`, which tests
-- `x ≟ ht`), so the sync fires at the CLIENT's own recorded header.  T5's
-- `LiveCSRow.cscRfwLands` pays the same gate one layer up.
--
-- *** WHAT THIS LEAVES, AND IT IS THE LEAF's HONEST RESIDUAL: FOUR positions of
-- `CliPost`'s five. ***  `cliPost-cp1-rest` below is the dispatch, and the four
-- are exactly T9-verify's table: `ccWreq` (a full cell holding a non-request),
-- `ccAwait` and `ccMust` (each needing the relay's own dn CS server region at
-- `pp3` plus a payload correlation) and `ccArb pt` (which needs an EXCLUSION, not
-- a refutation — `consD-no-rb` says its only api row is a label `consume` never
-- offers).  None of the four is closed here and none is claimed to be.
------------------------------------------------------------------------

-- the CS CLIENT at a position coarsening to `ccArf ht` accepts the rollforward
-- delivery its own driver offers (`csCnxt (ccArf (h , t))`, `NodeSpecs:359-365`;
-- the row is `ceqCSc15` and it is VALUE-GATED, so the client's own pair is what
-- fires).  §3's `peer-cD0` at the third of `ccArf`'s rows instead of `ccIdle`'s
-- first
peer-cD1 : (i : Link) (d : Dir) (q : SN.CScPos) (h : Header) (t : Tip)
         → coarsenCSc q ≡ NS.ccArf (h , t)
         → absCSc i d q
             ─[ ev (evl (evLabel (Header × Tip) (apiCS i d recvCSRollforward) (h , t))) ]─►
           absCSc i d (SN.csHead CS.stIdle)
peer-cD1 i d q h t pin =
  aCSc i d q (SN.csHead CS.stIdle)
    (subst (λ z → NS.csCfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.csCnxt i d z (_ , apiCS i d recvCSRollforward) (h , t)
                  ≡ just NS.ccIdle)
           (sym pin) (ceqCSc15 {h} {t} i d))

-- node D's consume driver at `cp1` offers the rollforward at EVERY value — an
-- INPUT prefix, so the successor is the value's own continuation and is returned
-- existentially
consVis-cp1 : (l : Link) (b₀ : Block₃) (h : Header) (t : Tip)
  → Σ[ P ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃ ]
      (viewV (PTree.force (decCons l hi b₀ cp1))
             ((Header × Tip) , apiCS l hi recvCSRollforward) (h , t) ≡ just P)
consVis-cp1 l b₀ h t rewrite ≟-yes-refl l = _ , refl

-- … and so the whole `consume l hi >> Skip` driver does
consD-offer-rfw : (l : Link) (b₀ : Block₃) (h : Header) (t : Tip)
  → IoOffers (decConsD l (consD b₀ cp1)) (apiCS l hi recvCSRollforward) (h , t)
consD-offer-rfw l b₀ h t =
    _
  , TLB.bind-ev (λ _ → Skip) (decCons l hi b₀ cp1)
      (sVis refl (proj₂ (consVis-cp1 l b₀ h t)))

-- *** THE REFUTATION OF THE LEAF's `ccArf` MEMBER, leg BD. ***  a STABLE
-- configuration cannot have node D's dn CS client at `ccArf ht` while node D's own
-- consume driver is at `cp1`
cliArf-cp1-BD-⊥ : (r : RState) (b₀ : Block₃) (h : Header) (t : Tip)
  → coarsenCSc (SN.NodeStateD.csC-BD (nD (toSys r))) ≡ NS.ccArf (h , t)
  → SN.NodeStateD.cons-BD (nD (toSys r)) ≡ consD b₀ cp1
  → isStable (radec r ∖ hidden blkA) → ⊥
cliArf-cp1-BD-⊥ r b₀ h t pin hcons sta =
  syncD-BD r aicCS ahlCS aicCSroll refl (λ ()) tt
    (absBundle-CSc-ev linkBD hi lo
       (SN.NodeStateD.csC-BD (nD (toSys r))) (SN.NodeStateD.csS-BD (nD (toSys r)))
       (SN.NodeStateD.bfC-BD (nD (toSys r))) (SN.NodeStateD.bfS-BD (nD (toSys r)))
       (SN.NodeStateD.inert-BD (nD (toSys r)))
       {e₁ = CS.apiCSev linkBD hi recvCSRollforward} {qcc′ = SN.csHead CS.stIdle}
       (λ ()) refl
       (peer-cD1 linkBD hi (SN.NodeStateD.csC-BD (nD (toSys r))) h t pin))
    (subst (λ q → IoOffers (decConsD linkBD q) (apiCS linkBD hi recvCSRollforward) (h , t))
           (sym hcons) (consD-offer-rfw linkBD b₀ h t))
    sta

-- … the CD-leg mirror
cliArf-cp1-CD-⊥ : (r : RState) (b₀ : Block₃) (h : Header) (t : Tip)
  → coarsenCSc (SN.NodeStateD.csC-CD (nD (toSys r))) ≡ NS.ccArf (h , t)
  → SN.NodeStateD.cons-CD (nD (toSys r)) ≡ consD b₀ cp1
  → isStable (radec r ∖ hidden blkA) → ⊥
cliArf-cp1-CD-⊥ r b₀ h t pin hcons sta =
  syncD-CD r aicCS ahlCS aicCSroll refl (λ ()) tt
    (absBundle-CSc-ev linkCD hi lo
       (SN.NodeStateD.csC-CD (nD (toSys r))) (SN.NodeStateD.csS-CD (nD (toSys r)))
       (SN.NodeStateD.bfC-CD (nD (toSys r))) (SN.NodeStateD.bfS-CD (nD (toSys r)))
       (SN.NodeStateD.inert-CD (nD (toSys r)))
       {e₁ = CS.apiCSev linkCD hi recvCSRollforward} {qcc′ = SN.csHead CS.stIdle}
       (λ ()) refl
       (peer-cD1 linkCD hi (SN.NodeStateD.csC-CD (nD (toSys r))) h t pin))
    (subst (λ q → IoOffers (decConsD linkCD q) (apiCS linkCD hi recvCSRollforward) (h , t))
           (sym hcons) (consD-offer-rfw linkCD b₀ h t))
    sta

-- *** THE LEG-DISPATCHED FORM. ***  §3's `cliIdle-cp0-⊥` shape at the other
-- sub-phase, and the leg dispatch is explicit for its reason
cliArf-cp1-⊥ : (l : TwoLegs) (r : RState) (b₀ : Block₃) (h : Header) (t : Tip)
  → dnCScC l (toSys r) ≡ NS.ccArf (h , t)
  → phOf l (toSys r) ≡ cp1
  → cblkOf l (toSys r) ≡ b₀
  → isStable (radec r ∖ hidden blkA) → ⊥
cliArf-cp1-⊥ legBD r b₀ h t pin hph hbk =
  cliArf-cp1-BD-⊥ r b₀ h t pin (consD-η (SN.NodeStateD.cons-BD (nD (toSys r))) hph hbk)
cliArf-cp1-⊥ legCD r b₀ h t pin hph hbk =
  cliArf-cp1-CD-⊥ r b₀ h t pin (consD-η (SN.NodeStateD.cons-CD (nD (toSys r))) hph hbk)

-- *** THE LEAF's RESIDUAL, AS A DISPATCH — four positions, not five. ***  The
-- `cp1` region minus the member §6f just refuted.  Stated so a successor reads
-- the remaining obligation off a type rather than off a report, and so that a
-- narrowing of `CliPost` (which is what a full `cp1` discharge must buy — F84's
-- re-aiming note) is a coverage error here
cliPost-cp1-rest : (ca : NS.CScPos) → CliPost ca
                 → ((h : Header) (t : Tip) → ca ≡ NS.ccArf (h , t) → ⊥)
                 → (ca ≡ NS.ccWreq) ⊎ (ca ≡ NS.ccAwait) ⊎ (ca ≡ NS.ccMust)
                   ⊎ (Σ[ pt ∈ Point × Tip ] (ca ≡ NS.ccArb pt))
cliPost-cp1-rest NS.ccIdle       () _
cliPost-cp1-rest NS.ccWreq       _  _  = inj₁ refl
cliPost-cp1-rest NS.ccAwait      _  _  = inj₂ (inj₁ refl)
cliPost-cp1-rest (NS.ccWfi ps)   () _
cliPost-cp1-rest NS.ccInt        () _
cliPost-cp1-rest NS.ccWdone      () _
cliPost-cp1-rest NS.ccMust       _  _  = inj₂ (inj₂ (inj₁ refl))
cliPost-cp1-rest (NS.ccArf ht)   _  no = ⊥-elim (no (proj₁ ht) (proj₂ ht) refl)
cliPost-cp1-rest (NS.ccArb pt)   _  _  = inj₂ (inj₂ (inj₂ (pt , refl)))
cliPost-cp1-rest (NS.ccAif pt)   () _
cliPost-cp1-rest (NS.ccAin tp)   () _
cliPost-cp1-rest NS.ccTerm       () _

------------------------------------------------------------------------
-- §6g  (T11) *** THE `pp3` LEAF's TWO REGIONS — the shapes T9's items (i) and the
-- correlation are stated at, and the ONLY new definitions the leaf's closure
-- needs. ***
--
-- `LiveRelayCS` §2e is the consumer: it dispatches on these two and closes the
-- leaf modulo THREE named facts.  They are defined HERE, beside `CliPost` and
-- §6f, because they are ChainSync-hop shapes and this is the ChainSync-hop file.
--
-- WHY THESE TWO REGIONS AND NOT OTHERS — the derivation, which is worth more than
-- the four lines below and was the expensive part of (T11) round 2:
--
--   · THE SERVER REGION `SrvRfw` = `{csWrf ht, csIdle}`.  At `producing _ pp3` the
--     relay has fired `sendCSRollForward`, whose row lands its down CS server at
--     `csWrf ht` (`csSnxt csMust … ≡ just (csWrf ht)`), and the server's own
--     wire-send takes it on to `csIdle` (`ceqCSs14`).  Nothing else is reachable
--     while the phase is `pp3`: the api exits need the driver's other labels and
--     the `csIdle` READ needs a request in the cell, which the CELL region
--     forbids.  *** IT IS NOT io-CLOSED BY ITSELF and that is the point *** — F88's
--     rule one protocol over: the region is closed only WITH the cell conjunct,
--     exactly as `LiveDrvBFD`'s client region is (its §0(5)).
--   · THE CELL REGION `CellRfw` = `empty ⊎ draining ⊎ ArOnly ⊎ RfwOnly`.  Both
--     responder payloads are genuinely possible at `pp3`: the `MsgCSAwaitReply`
--     the server wrote at `csWar` may still be unread (which is why `csMust` is in
--     the `pp2` region at all), and the `MsgCSRollForward` is what the arm's own
--     entering step will put on the wire.  *** NO OTHER MESSAGE CAN BE THERE: ***
--     `produce` never fires `sendCSRollBackward` or the two intersect replies, and
--     node D's own request was read long before (the server is past `csAreq`).
--
-- *** AND THE THREE FACTS THE LEAF STILL NEEDS, WITH THE REASON EACH IS
-- IRREDUCIBLE — this is the round's real finding. ***  `LiveRelayCS` §2e states
-- them as premises; each is a CORRELATION between the cell and node D's client,
-- and NONE of them is derivable from positions alone:
--
--   (X) an unread `MsgCSAwaitReply` ⇒ node D's client is at `ccAwait`.
--   (Y) an unread `MsgCSRollForward` ⇒ it is at `ccAwait` or `ccMust`.
--   (Z) an EMPTY cell with the server at `csIdle` ⇒ it has CONSUMED the
--       rollforward (`ccArf ht`, or `ccIdle` past the api step).
--
-- WHY NOT `ChanCS`: its three clauses are all SrvPre- or ReqFull-antecedent (the
-- server side and the REQUEST), and there is no responder-payload clause at all.
-- WHY NOT DERIVABLE AT `pp3`: every route bottoms out at `csMust`, where
-- `SrvPre csMust = ⊥` (`LiveChanCS:246`, and F31 records that widening it is
-- FALSE) — so at the arm's own entering step the invariant says nothing about the
-- client, and the correlation has to have been CARRIED there.  WHY THEY ARE NOT
-- `pp3`-local either: (X) must survive the server's write at `csWar` (where
-- `ccPre` DOES supply `CliAwt`, so (X) is establishable — but that step is at
-- `pp2`, outside a `{pp3}` guard).  *** SO THE THREE ARE ONE HOP-LOCAL EXTENSION
-- OF `ChanCS` (a responder-payload antecedent, ≈24 `mkChanCS` producer sites and
-- the five-class calculus) PLUS the `pp3`-guarded (Z), and that is the honest
-- remaining shape of T9's items (i)+(iii) and its correlation. ***
--
-- *** POSTSCRIPT (T11, round 2) — THIS IS SUPERSEDED IN ITS CONCLUSION, AND THE
-- CORRECTION IS THE ROUND'S REAL FINDING: THE `ChanCS` EXTENSION IS NOT NEEDED.
-- WIDEN THE GUARD BY ONE SUB-PHASE INSTEAD. ***  The paragraph above is right that
-- nothing establishes the correlations AT `pp3`; it is wrong to conclude that they
-- must therefore be hop-local, and the reason is the guard region's LEFT end:
--
--   · with the guard `{producing _ pp3}` the entering step is the relay's own
--     `sendCSRollForward`, whose SOURCE server is `csMust` — and `SrvPre csMust` is
--     `⊥`, so `ChanCS` says nothing there.  That is the dead end above.
--   · with the guard `{producing _ pp2, producing _ pp3}` the entering step is the
--     relay's `sendCSAwaitReply` at `pp1 → pp2`, whose LANDING IS ALREADY BUILT
--     (`LiveLegApiCone.DnCsAwLand`, T6d, carried in `DnCsDrv`'s landing pair) and
--     lands the server at `csWar` — which IS in `SrvPre`.  There `ccQui` gives the
--     cell (`empty`/`draining`) and `ccPre` the client (`CliAwt`), so *** all three
--     correlations are VACUOUS at the entering step and each is established later
--     at the very step that creates its own antecedent: *** (X) at the server's
--     `csWar → csMust` write (the client is fixed and the source's conjunct is
--     `CliAwt`), (Y) at its `csWrf → csIdle` write, (Z) at the client's own read
--     that empties the cell.  *** A RECORD's FIELDS MAY SUPPORT EACH OTHER; A
--     HOP-LOCAL CLAUSE'S MAY NOT — and that is the whole difference. ***
--
-- *** WHAT SURVIVES AS IRREDUCIBLE IS ONE THING: THE `pp3` LANDING. ***  With the
-- wider guard the server region is `{csWar, csMust, csWrf ht, csIdle}`, and
-- `(pp3 , csMust , empty , ccMust)` is then admitted — a configuration checked
-- component by component to be GENUINELY STUCK (the relay's driver at `pp3` offers
-- only `apiBF reqBFRange` and the dn BF server has no api row; the CS server at
-- `csMust` offers only api labels the driver no longer offers and has no io row;
-- the cell is empty; node D's client at `ccMust` has no `recvCSRollforward` row and
-- its BF client no partner at `cp1`).  It is unreachable for exactly ONE reason —
-- the relay cannot have advanced to `pp3` without its own server co-firing the
-- `apiES` sync — and that reason is a BUNDLE-level fact: `DnCsDrv`'s landing pair
-- needs a THIRD member.  So T9's item (i) reduces to that one cone landing (whose
-- type MOVES `DnCsDrv` and therefore ripples to `LiveLegApiExpose`, `LiveDrvBF`
-- and the carry), and everything else the leaf needs is a record with a
-- two-sub-phase guard whose establishment is already carried.
------------------------------------------------------------------------

-- the relay's own down CS server, at `producing _ pp3`: it has fired the
-- rollforward and has at most wire-sent it
SrvRfw : NS.CSsPos → Set
SrvRfw NS.csIdle       = ⊤
SrvRfw NS.csAreq       = ⊥
SrvRfw NS.csCanAwait   = ⊥
SrvRfw (NS.csAfi ps)   = ⊥
SrvRfw NS.csInt        = ⊥
SrvRfw NS.csDdone      = ⊥
SrvRfw NS.csMust       = ⊥
SrvRfw (NS.csWrf ht)   = ⊤
SrvRfw (NS.csWrb pt)   = ⊥
SrvRfw NS.csWar        = ⊥
SrvRfw (NS.csWif pt)   = ⊥
SrvRfw (NS.csWin tp)   = ⊥
SrvRfw NS.csTerm       = ⊥

-- the two-way dispatch the leaf's `empty` arm runs on
srvRfw-cases : (q : NS.CSsPos) → SrvRfw q
             → (q ≡ NS.csIdle) ⊎ (Σ[ ht ∈ Header × Tip ] (q ≡ NS.csWrf ht))
srvRfw-cases NS.csIdle       _  = inj₁ refl
srvRfw-cases NS.csAreq       ()
srvRfw-cases NS.csCanAwait   ()
srvRfw-cases (NS.csAfi ps)   ()
srvRfw-cases NS.csInt        ()
srvRfw-cases NS.csDdone      ()
srvRfw-cases NS.csMust       ()
srvRfw-cases (NS.csWrf ht)   _  = inj₂ (ht , refl)
srvRfw-cases (NS.csWrb pt)   ()
srvRfw-cases NS.csWar        ()
srvRfw-cases (NS.csWif pt)   ()
srvRfw-cases (NS.csWin tp)   ()
srvRfw-cases NS.csTerm       ()

-- the cell holds the server's unread `MsgCSAwaitReply` — `ReqOnly`'s shape at the
-- responder's first message, and LENIENT in the tuple's other three components
ArOnly : SM.CopyPhase → Set
ArOnly ph = FullMsg ph MsgCSAwaitReply

-- … and its unread `MsgCSRollForward`, existential in the header/tip pair the
-- relay's own driver supplied
RfwOnly : SM.CopyPhase → Set
RfwOnly ph = Σ[ h ∈ Header ] Σ[ tp ∈ Tip ] FullMsg ph (MsgCSRollForward h tp)

-- the hop's cell at `producing _ pp3`: four arms, and they are exactly the four
-- the leaf's dispatch runs on
CellRfw : SM.CopyPhase → Set
CellRfw ph = (ph ≡ SM.empty)
           ⊎ (Σ[ x ∈ Payload ] (ph ≡ SM.draining x))
           ⊎ ArOnly ph
           ⊎ RfwOnly ph

------------------------------------------------------------------------
-- §6h  (T11, round 3) *** THE `{pp2, pp3}`-GUARDED RECORD — ITS TYPE, AND WHERE
-- EVERY FIELD IS ESTABLISHED.  This is the object T9-verify called "a second
-- `DnFreshC`, one guard over", and §6g's postscript is the finding that made it
-- affordable. ***
--
-- The guard is `{producing _ pp2, producing _ pp3}`, so the ENTERING STEP is the
-- relay's `sendCSAwaitReply` at `pp1 → pp2`, whose landing is ALREADY BUILT AND
-- CARRIED (`LiveLegApiCone.DnCsAwLand`, T6d) and lands the down CS server at
-- `csWar` — the one position in `SrvPre` on this stretch, where `LiveChanCS`'s
-- `ccQui` gives the cell and `ccPre` the client for free.  Every field below is
-- therefore VACUOUS or FREE at the entering step, and each becomes substantive
-- exactly at the step that creates its own antecedent.
--
-- *** THE FIELD MAP — established WHERE, preserved BY WHAT.  This is the design in
-- full; a successor transcribes §5's calculus against it and nothing more. ***
--
--  1 `rwSrv` the server's phase-indexed region — `{csWar, csMust}` at `pp2`
--    (T6d's own `DrvCp` region) and `{csWrf ht, csIdle}` at `pp3` (§6g's `SrvRfw`).
--    ESTABLISHED: at the entering step by `DnCsAwLand` (`csWar`).  PRESERVED: by the
--    server's io rows inside each phase (`csWar → csMust`, `csWrf → csIdle`), and
--    ACROSS `pp2 → pp3` *** ONLY BY THE `pp3` LANDING — the one irreducible cone
--    item (§6g's postscript). ***  The `csIdle` READ that would leave the region is
--    refuted by field 3.
--  2 `rwCli` the client's region, WIDE: everything but `ccWreq`, `ccWfi`, `ccArb`,
--    `ccAif`, `ccAin`.  ESTABLISHED: `ccPre` at `csWar` (`CliAwt ⊆` the region).
--    PRESERVED: the four omitted `CliDrvAdj` rows do not exist (§5's own note:
--    `consD-no-fi`/`-rb`/`-if`/`-in`), and `ccWreq`'s only entry is `cdReq` at
--    `cp0`, refuted by field 4.
--  3 `rwCell` §6g's four-armed cell region.  ESTABLISHED: `ccQui` at `csWar`
--    (`empty`/`draining`).  PRESERVED: the server's two writes land in `ArOnly` and
--    `RfwOnly`; every read drains; no other writer exists on this hop.
--  4 `rwPh`  node D's phase is past `cp0`.  ESTABLISHED: `ccPre` at `csWar` gives
--    `CliAwt`, so the client is not at `ccIdle`, and `DrvCliD`'s `cp0` clause
--    contraposes to `x ≢ cp0`.  PRESERVED: nothing ever lands at `cp0` (`ConsAdv`'s
--    six targets are `cp1 … cp6`).  *** THIS IS THE ORDER FACT, and it is free here
--    and nowhere else — at a `{pp3}`-only guard the entering step's server is
--    `csMust`, where `SrvPre` is `⊥`. ***
--  5 `rwAr`  an unread `MsgCSAwaitReply` ⇒ `CliAwt ca`.  ESTABLISHED: at the
--    server's own `ssAR` write, from `ccPre` at the source `csWar`.  PRESERVED: the
--    client's read drains the cell, killing the antecedent.
--  5b `rwRfw` an unread `MsgCSRollForward` ⇒ `CliAwt ca ⊎ ca ≡ ccMust`.
--    ESTABLISHED: at the server's `ssRF` write — *** and this is the field FIELD 7
--    EXISTS FOR: *** at that step the source server is `csWrf ht`, where `SrvPre` is
--    `⊥` and the channel invariant says nothing, so the client fact has to come from
--    the record itself.  PRESERVED: the client's read drains the cell.
--  5c `rwWar` the server at `csWar` ⇒ `CliAwt ca`.  ESTABLISHED: `ccPre` at the
--    entering step, where it is the landing's own position.  PRESERVED: at `csWar`
--    the cell is pre-region (`ccQui`), so the client has nothing to read and
--    `ccAwait` has no write row — it cannot leave `CliAwt` while the server stays.
--    *** It is what field 5 is established FROM, at the server's own `ssAR` write. ***
--  6 `rwMst` the server at `csMust` ⇒ `CliAwt ca ⊎ ca ≡ ccMust`.  ESTABLISHED: at
--    the same `ssAR` write.  PRESERVED: the client's read of the `ar` lands in the
--    right disjunct; its other rows need a payload the cell region excludes.
--  7 `rwWrf` the server at `csWrf ht` ⇒ `CliAwt ca ⊎ ca ≡ ccMust`.  ESTABLISHED: at
--    the `pp2 → pp3` landing, from field 6 (the source is `csMust`) or `ccPre` (the
--    source is `csWar`).  PRESERVED: as field 6.
--  8 `rwEmp` an EMPTY cell at `csIdle` ⇒ the client has CONSUMED the rollforward.
--    *** ITS CONCLUSION IS DELIBERATELY WIDE — `ccArf ht ⊎ ccIdle ⊎ ccWdone ⊎
--    ccTerm` — and that width is what makes it preservable: *** node D's `cdDone`
--    hop lands the client at `ccWdone` and its own write at `ccTerm`, and both are
--    inside.  At the LEAF the extra two are killed for free by the carried
--    `CliPost` (`cp1` admits neither), so the width costs the consumer nothing.
--    ESTABLISHED: at the client's read that empties the cell (`ccArf`).
--
-- *** WHAT THE CALCULUS WILL ADD, AND WHY — traced class by class (T11 round 3,
-- while checking the io arms against the ten fields above; recorded so the
-- transcription does not rediscover it). ***  The ten fields are exactly what the
-- LEAF needs; the PRESERVATION needs four more, and every one of them is a
-- cell⇒server or server⇒cell correlation that is FREE at the step that creates its
-- own antecedent:
--
--   · `rwRfwS : RfwOnly ph → sa ≡ csIdle` — an unread rollforward means the server
--     has WRITTEN it, so it is at `csIdle`.  NEEDED BY: the client's read class
--     (`crRF`/`crMRF`), whose successor client `ccArf ht` is outside `CliAwt` and
--     not `ccMust`, so fields 5c/6/7 can only be preserved by refuting their
--     ANTECEDENTS — and this is what refutes them.  FREE at the `ssRF` write.
--   · `rwArS : ArOnly ph → sa ≡ csWar → ⊥` — likewise for the `crAR` arm.  FREE at
--     the `ssAR` write (its successor is `csMust`).
--   · field 5c's conclusion GAINS `CellPreQ ph` (the server at `csWar` has an
--     empty-or-draining cell, `ccQui`'s own content).  NEEDED BY: the same read
--     class, to refute a `full` cell at a `csWar` server.  FREE at the entering step
--     — it is `ccQui` at the landing, already in hand there.
--   · field 8 (`rwEmp`) GENERALISES its antecedent from `ph ≡ empty` to
--     `CellPreQ ph`.  NEEDED BY: the medium's DRAIN class, which turns `draining`
--     into `empty` and would otherwise have to invent the client's position out of
--     nothing.  With the wider antecedent the drain is a pure transport.
--
-- *** SO THE RECORD IS TWELVE FIELDS, and the extra two-and-a-half are all of the
-- same species as fields 5c-7: the hop's two components pinning each other, each
-- established at the write that creates it.  THE LEAF's INTERFACE (§2f) IS
-- UNAFFECTED — it consumes the ten. ***
--
-- *** AND ONE MORE STRUCTURAL REQUIREMENT, FOUND BY TRACING THE CLIENT's OWN
-- WRITE CLASS — read this before writing the calculus, because it decides where the
-- calculus can live. ***
--
-- FIELD 4 CANNOT BE "`x ≢ cp0`"; IT MUST BE THE REGION `{cp1, cp2, cp3}`.  The
-- client's own `csDone` row (`ccIdle → ccWdone`, fired by node D's driver at `cp5`)
-- puts a `MsgCSDone` in the cell — a payload the cell region (field 3) does not
-- admit, and MUST NOT admit: widening it re-opens the leaf, because neither
-- `ccAwait` nor `ccMust` has a read row for a done and the configuration would be
-- stuck again.  So the class has to refute the row, and the only thing that refutes
-- it is node D's phase.
--
-- ESTABLISHING the region is free (the token's `InCp03` at the entering step, and
-- `PipeInv` is carried).  *** PRESERVING it is NOT local: *** the hop that leaves
-- the region is node D's `cp3 → cp4`, its own `recvBFBlock`, and what refutes THAT
-- is the BlockFetch client's position — `LiveDrvBFD.BFFresh`'s client conjunct,
-- whose api class already refutes the same hop as `BFCliDrvAdj`'s `dbRecv` arm.
-- So the api class must be the PAIR's (`BFFresh × DnRfwC`), taking BOTH joint
-- adjacencies: the `UpJoint = UpBd × UpCli` precedent, where one component's
-- conjunct preserves the other's.
--
-- *** CONSEQUENCE, AND IT IS WHY (T11) STOPPED HERE: *** the calculus is then the
-- twelve fields × eight classes with a 29-clause `SrvAtRfw`-transport dispatch (the
-- server's FILL class is the one that needs the relay-phase index), a PAIRED api
-- class, and eight state-level wrappers — 350-450, which crosses the round's
-- authorised trigger.  Nothing above is speculative: every field is consumed by
-- §2f or by a class arm named in this map.
--
-- *** <<< SUPERSEDED (T11 fix round, review C-1) — THE SENTENCE ABOVE IS QUOTED SO
-- A COPY CANNOT REINTRODUCE IT, AND IT IS FALSE IN ITS CONCLUSION: *** "the api
-- class must be the PAIR's … the calculus cannot be written independently of the
-- ninth factor's pairing" and "350-450, which crosses the round's authorised
-- trigger".  *** THE COUPLING DOES NOT EXIST.  THE TRIGGER FIRED ON A PHANTOM. >>>
--
-- THE THREAT ANALYSIS ABOVE IS SOUND — field 4 as landed does not exclude `cp5`,
-- `csDone` does fire there, `CellRfw` does not admit a `MsgCSDone`, and widening it
-- would re-open the leaf.  What is wrong is WHERE the strengthening comes from.
--
-- *** THE ANATOMY OF THE PHANTOM, in one line: THE ROUND USED THE CARRIED TOKEN FOR
-- ESTABLISHMENT AND THEN WENT LOOKING FOR A SECOND OBJECT FOR PRESERVATION — BUT A
-- FACT DERIVED AT EACH STATE FROM A CARRIED INVARIANT UNDER THE GUARD HAS NOTHING
-- TO PRESERVE. ***  `RelayRfw` = `{producing _ pp2, producing _ pp3}` FORCES the
-- token to level `L2`: `relayP L0`/`L1` are `RelayPre`, `⊥` at every `producing`
-- (`PipeInv:127-135`); `relayP L3`/`L4` are `RelayFwd`, `⊥` at `pp2`/`pp3`
-- (`:159-171`); `relayP L2` is `RelayHas`, `⊤` at both.  And `consP L2 = InCp03`
-- (`:210-214`), which is `⊥` at `cp4`/`cp5`/`cp6` (`WalkPr:69-76`).  So at EVERY
-- state in this record's own guard, `InCp03 (phOf l s)` is FREE from the carried
-- `PipeInv` — and *** `PhRfwD x ∧ InCp03 x` IS EXACTLY the region `{cp1, cp2, cp3}`
-- ***, with the three leaving hops refuted at their SUCCESSOR by the token alone.
-- No `BFFresh` conjunct anywhere; the api class is SINGLE-OBJECT; D′ is
-- checkpointable BEFORE I.  The shape to copy is `LiveRelayCS.pipeInv⇒sent-cp4`
-- (`:462-469`) — the same five-clause level elimination at `consuming _ cp4`, T10's
-- headline — and the supply is the banked projection
-- `LegJoint → PipeInvS → PipeInv⁺ → PipeInv`.
--
-- *** THE GUARD LAW GAINS A CLAUSE, and it is this task's own lesson: *** the
-- standing law says evaluate the guard at the arm's sub-phase, at the region's
-- entering step, and at every advance with both ends inside.  ADD: *** for each
-- fact the object is about to CARRY, ask whether the guard already DERIVES it from
-- something carried — check derivation-vs-carry BEFORE re-costing. ***  A derived
-- fact needs no field, no class arm and no pairing; a carried one needs all three.
-- T9's §5b(4) does not block this and was checked: `token-⊮-pp3-cp1` says the token
-- cannot separate `pp3` from node D's `cp1` (both admitted) — a statement about the
-- LEAF's own sub-phase, not about excluding `cp4`/`cp5`/`cp6`.
--
-- *** THE CORRECTED D′ MAP (what T11b lands; ~45 lines, review-probed GREEN FIRST
-- TRY at ≈18.6s).  FIELD 4 STAYS EXACTLY AS LANDED — the region is `PhRfwD ∧
-- InCp03`, the second half DERIVED per state, never a record field: ***
--
--   `relayRfw-cases     : (x : CPPh) → RelayRfw x`
--   `                   → (Σ[ b ] x ≡ producing b pp2) ⊎ (Σ[ b ] x ≡ producing b pp3)`
--        — 12 clauses, the guard's own two-way dispatch
--   `pipeInv⇒inCp03-pp2 : … relayOf l s ≡ producing b pp2 → PipeInv l s`
--   `                   → InCp03 (phOf l s)`   — 5 clauses, `pipeInv⇒sent-cp4`'s shape
--   `pipeInv⇒inCp03-pp3 : …` the same at `pp3`  — 5 clauses
--   `relayRfw⇒inCp03    : … RelayRfw (relayOf l s) → PipeInv l s → InCp03 (phOf l s)`
--        — the wrapper the classes call
--
-- and the calculus comes back to 260-370 (round 3's specified 250-350 plus the
-- measured 45), api class SINGLE-OBJECT, `I` checkpointable AFTER it.
--
-- *** WHAT THE LEAF USES, and it is why the fields are shaped as they are: ***
-- `LiveRelayCS` §2f dispatches on `rwCell` and, at the empty cell, on `rwSrv`; the
-- three correlations 5/7/8 turn each surviving cell into a client position the io
-- ladders or §6f can refute; and `CliPost` ∧ `CliAwt` ⇒ `ccAwait`
-- (`cliAwt-post⇒await` below) is the one-line bridge that makes the reader
-- refutations applicable.
------------------------------------------------------------------------

-- node D's phase is past its own request — the ORDER fact, as a dispatch
PhRfwD : ConsPh → Set
PhRfwD cp0 = ⊥
PhRfwD cp1 = ⊤
PhRfwD cp2 = ⊤
PhRfwD cp3 = ⊤
PhRfwD cp4 = ⊤
PhRfwD cp5 = ⊤
PhRfwD cp6 = ⊤

-- the client's region on this stretch: it has requested, and it has not yet begun
-- its own done.  The excluded positions are the ones whose entry `CliDrvAdj` has no
-- row for (`ccWfi`, `ccAif`, `ccAin`, `ccArb`), whose entry field 4 refutes
-- (`ccWreq`), or whose entry the CARRIED TOKEN refutes (`ccWdone` and `ccTerm`).
--
-- *** (T11b) `ccWdone` AND `ccTerm` ARE NOW OUT, and that narrowing is what closes
-- round 4's threat. ***  The round-3 map had both INSIDE, on the grounds that "node
-- D's `cdDone` hop lands the client at `ccWdone` and its own write at `ccTerm`".
-- `cdDone` fires at `cp5`, where the carried token's `InCp03` is `⊥` (review C-1),
-- so the hop is REFUTED and neither position is reachable inside the guard — and
-- with `ccWdone` out, the client's own `csDone` WIRE-SEND is refuted at its SOURCE,
-- which is what keeps its `MsgCSDone` out of field 3's cell region.  Round 4 went
-- looking for a correlation to do that; the region was enough.  *** Re-widening
-- either clause re-opens the leaf, by way of `dnRfw-cliSend`'s third row. ***
CliRfwReg : NS.CScPos → Set
CliRfwReg NS.ccIdle       = ⊤
CliRfwReg NS.ccWreq       = ⊥
CliRfwReg NS.ccAwait      = ⊤
CliRfwReg (NS.ccWfi ps)   = ⊥
CliRfwReg NS.ccInt        = ⊤
CliRfwReg NS.ccWdone      = ⊥
CliRfwReg NS.ccMust       = ⊤
CliRfwReg (NS.ccArf ht)   = ⊤
CliRfwReg (NS.ccArb pt)   = ⊥
CliRfwReg (NS.ccAif pt)   = ⊥
CliRfwReg (NS.ccAin tp)   = ⊥
CliRfwReg NS.ccTerm       = ⊥

-- the server's region, INDEXED BY THE RELAY's PHASE: T6d's `pp2` region and §6g's
-- `pp3` one, and `⊤` wherever the guard does not reach.
--
-- *** KEEP IN SYNC — `LiveDrvBF.DrvCp l s (producing _ pp2)` (`LiveDrvBF:310-311`).
-- THE `pp2` CLAUSE BELOW IS A HAND COPY OF THAT ALREADY-CARRIED CLAUSE
-- (`LegJointU`'s fifth factor), and the duplication is in a clause BODY, so a
-- NARROWING of `DrvCp`'s region (which `LiveRelayCS.csRegion⇒must` exists precisely
-- to sharpen) would diverge from this copy SILENTLY — no coverage error, no type
-- error, because `DrvCp`'s own header only promises coverage protection for the
-- CONSTRUCTOR set. ***  (T11 review's I-5.)  The alternative, banked for T11b as its
-- FIRST CHEAP WIN and deliberately NOT taken here: make this clause `⊤` and read
-- the `pp2` region off the carried `DrvCp` instead — which also removes one field's
-- establishment obligation and one clause-set from the transport dispatch, an
-- unmeasured −20-40
SrvAtRfw : CPPh → NS.CSsPos → Set
SrvAtRfw (consuming b x)   sa = ⊤
SrvAtRfw (producing b pp0) sa = ⊤
SrvAtRfw (producing b pp1) sa = ⊤
SrvAtRfw (producing b pp2) sa = (sa ≡ NS.csWar) ⊎ (sa ≡ NS.csMust)
SrvAtRfw (producing b pp3) sa = SrvRfw sa
SrvAtRfw (producing b pp4) sa = ⊤
SrvAtRfw (producing b pp5) sa = ⊤
SrvAtRfw (producing b pp6) sa = ⊤
SrvAtRfw (producing b pp7) sa = ⊤
SrvAtRfw (producing b pp8) sa = ⊤
SrvAtRfw (producing b pp9) sa = ⊤

-- *** THE RECORD. ***  Five components — the hop's three, node D's phase and the
-- RELAY's phase — and TWELVE fields (1, 2, 3, 4, 5, 5b, 5c, 6, 7, 8, 9, 10), all
-- mapped in the header above.  (T11 review's M-3: this comment read "eight"; T11
-- landed the first TEN and (T11b) added the map's own traced two.)
record DnRfwC (sa : NS.CSsPos) (ph : SM.CopyPhase) (ca : NS.CScPos)
              (x : ConsPh) (rx : CPPh) : Set where
  constructor mkDnRfwC
  field
    rwSrv  : SrvAtRfw rx sa
    rwCli  : CliRfwReg ca
    rwCell : CellRfw ph
    rwPh   : PhRfwD x
    rwAr   : ArOnly ph → CliAwt ca
    rwRfw  : RfwOnly ph → CliAwt ca ⊎ (ca ≡ NS.ccMust)
    -- (T11b) the conclusion GAINS `CellPreQ ph` — `ccQui`'s own content at the
    -- landing, free at the entering step, and what refutes a `full` cell at a
    -- `csWar` server in the client's read class
    rwWar  : sa ≡ NS.csWar → CliAwt ca × CellPreQ ph
    rwMst  : sa ≡ NS.csMust → CliAwt ca ⊎ (ca ≡ NS.ccMust)
    rwWrf  : (ht : Header × Tip) → sa ≡ NS.csWrf ht
           → CliAwt ca ⊎ (ca ≡ NS.ccMust)
    -- (T11b) the ANTECEDENT generalises from `ph ≡ empty` to `CellPreQ ph`, which
    -- is what makes the medium's DRAIN class a pure transport; and the CONCLUSION
    -- loses its `ccWdone`/`ccTerm` disjuncts, which the narrowed `CliRfwReg` has
    -- made unreachable inside the guard
    rwEmp  : CellPreQ ph → sa ≡ NS.csIdle
           → (Σ[ ht ∈ Header × Tip ] (ca ≡ NS.ccArf ht)) ⊎ (ca ≡ NS.ccIdle)
    -- (T11b) THE TWO EXTRA FIELDS the round-3 map's postscript traced: the hop's
    -- cell pinning its SERVER, each free at the write that creates its own
    -- antecedent, and each needed to refute fields 5c/6/7's ANTECEDENTS at the
    -- client's read arms — where the successor client is outside `CliAwt`
    rwRfwS : RfwOnly ph → sa ≡ NS.csIdle
    rwArS  : ArOnly ph
           → (sa ≡ NS.csMust) ⊎ (Σ[ ht ∈ Header × Tip ] (sa ≡ NS.csWrf ht))
open DnRfwC public

-- the guard: the two sub-phases the record covers.  `pp2` is where its entering
-- step lands and `pp3` is the arm's own — see §6g's postscript for why the left end
-- is `pp2` and not `pp3`
RelayRfw : CPPh → Set
RelayRfw (consuming b x)   = ⊥
RelayRfw (producing b pp0) = ⊥
RelayRfw (producing b pp1) = ⊥
RelayRfw (producing b pp2) = ⊤
RelayRfw (producing b pp3) = ⊤
RelayRfw (producing b pp4) = ⊥
RelayRfw (producing b pp5) = ⊥
RelayRfw (producing b pp6) = ⊥
RelayRfw (producing b pp7) = ⊥
RelayRfw (producing b pp8) = ⊥
RelayRfw (producing b pp9) = ⊥

-- *** THE GUARDED FORM — the shape the ninth `LegJointU` factor carries beside
-- `LiveDrvBFD.BFFresh` (the `UpJoint = UpBd × UpCli` precedent). ***
DnRfw : TwoLegs → SysState → Set
DnRfw l s = RelayRfw (relayOf l s)
          → DnRfwC (SStep.coarsenCSs (dnCSsOf l s)) (cellCSDn l s)
                   (dnCScC l s) (phOf l s) (relayOf l s)

-- the guard AT THE ARM's own sub-phase, so a consumer never computes it
relayRfw-pp3 : (l : TwoLegs) (s : SysState) (b : Block₃)
             → relayOf l s ≡ producing b pp3 → RelayRfw (relayOf l s)
relayRfw-pp3 l s b eq = subst RelayRfw (sym eq) tt

-- (T11e) … and at the guard's OTHER end, which the api arm's `pp3` branch needs at
-- the SOURCE (the in-guard advance comes out of `pp2`)
relayRfw-pp2 : (l : TwoLegs) (s : SysState) (b : Block₃)
             → relayOf l s ≡ producing b pp2 → RelayRfw (relayOf l s)
relayRfw-pp2 l s b eq = subst RelayRfw (sym eq) tt

-- *** THE ONE-LINE BRIDGE THE LEAF's READER REFUTATIONS NEED. ***  The record's
-- correlations conclude in `CliAwt` (which is what makes them establishable off
-- `ccPre`); the io ladders want the POSITION.  At the leaf the carried `CliPost`
-- supplies the difference: `ccInt`, `CliAwt`'s other member, is not in it
cliAwt-post⇒await : (ca : NS.CScPos) → CliAwt ca → CliPost ca → ca ≡ NS.ccAwait
cliAwt-post⇒await NS.ccIdle       () _
cliAwt-post⇒await NS.ccWreq       () _
cliAwt-post⇒await NS.ccAwait      _  _  = refl
cliAwt-post⇒await (NS.ccWfi ps)   () _
cliAwt-post⇒await NS.ccInt        _  ()
cliAwt-post⇒await NS.ccWdone      () _
cliAwt-post⇒await NS.ccMust       () _
cliAwt-post⇒await (NS.ccArf ht)   () _
cliAwt-post⇒await (NS.ccArb pt)   () _
cliAwt-post⇒await (NS.ccAif pt)   () _
cliAwt-post⇒await (NS.ccAin tp)   () _
cliAwt-post⇒await NS.ccTerm       () _

-- *** §6h's HELPERS AND ITS KEYSTONE. ***  What follows is NOT the preservation
-- calculus (that is the transcription the field map above specifies); it is the
-- three lemmas that decide whether the design is affordable at all — the guard's
-- total dispatch on a relay advance, and *** THE ENTERING STEP, which the finding
-- claims is FREE. ***  `dnRfw-enter` below is that claim, machine-checked.

-- an `empty` or `draining` cell holds no unread responder payload
arOnly-preQ-⊥ : (ph : SM.CopyPhase) → CellPreQ ph → ArOnly ph → ⊥
arOnly-preQ-⊥ ph (inj₁ refl)       (_ , _ , _ , ())
arOnly-preQ-⊥ ph (inj₂ (x , refl)) (_ , _ , _ , ())

rfwOnly-preQ-⊥ : (ph : SM.CopyPhase) → CellPreQ ph → RfwOnly ph → ⊥
rfwOnly-preQ-⊥ ph (inj₁ refl)       (_ , _ , _ , _ , _ , ())
rfwOnly-preQ-⊥ ph (inj₂ (x , refl)) (_ , _ , _ , _ , _ , ())

-- … and a pre-region cell IS one of the record's first two cell arms
cellPreQ⇒rfw : (ph : SM.CopyPhase) → CellPreQ ph → CellRfw ph
cellPreQ⇒rfw ph (inj₁ he)         = inj₁ he
cellPreQ⇒rfw ph (inj₂ (x , hd))   = inj₂ (inj₁ (x , hd))

-- the AWAITING region is inside the record's wide client region
cliAwt⇒reg : (ca : NS.CScPos) → CliAwt ca → CliRfwReg ca
cliAwt⇒reg NS.ccIdle       ()
cliAwt⇒reg NS.ccWreq       ()
cliAwt⇒reg NS.ccAwait      _  = tt
cliAwt⇒reg (NS.ccWfi ps)   ()
cliAwt⇒reg NS.ccInt        _  = tt
cliAwt⇒reg NS.ccWdone      ()
cliAwt⇒reg NS.ccMust       ()
cliAwt⇒reg (NS.ccArf ht)   ()
cliAwt⇒reg (NS.ccArb pt)   ()
cliAwt⇒reg (NS.ccAif pt)   ()
cliAwt⇒reg (NS.ccAin tp)   ()
cliAwt⇒reg NS.ccTerm       ()

-- … and an AWAITING client is not idle, which is what turns `DrvCliD`'s `cp0`
-- clause into the ORDER FACT
cliAwt-idle-⊥ : CliAwt NS.ccIdle → ⊥
cliAwt-idle-⊥ ()

-- *** THE GUARD's TOTAL DISPATCH ON A RELAY ADVANCE — three outcomes where
-- `LiveDrvBFD`'s had two, and the extra one is the ENTERING STEP this region has
-- and the BlockFetch twin does not (its region contains the initial phase; this one
-- starts at `pp2`). ***
data RfwStep : CPPh → CPPh → Set where
  rsEnter : (b : Block₃) → RfwStep (producing b pp1) (producing b pp2)
  rsAdv   : (b : Block₃) → RfwStep (producing b pp2) (producing b pp3)
  rsOut   : {x x′ : CPPh} → (RelayRfw x′ → ⊥) → RfwStep x x′

relayAdvRfw : (x x′ : CPPh) → RelayAdv x x′ → RfwStep x x′
relayAdvRfw _ _ (raCons b b′ c c′ _) = rsOut (λ ())
relayAdvRfw _ _ (raCp6 _)            = rsOut (λ ())
relayAdvRfw _ _ (raProd b _ _ a01)   = rsOut (λ ())
relayAdvRfw _ _ (raProd b _ _ a12)   = rsEnter b
relayAdvRfw _ _ (raProd b _ _ a23)   = rsAdv b
relayAdvRfw _ _ (raProd b _ _ a34)   = rsOut (λ ())
relayAdvRfw _ _ (raProd b _ _ a45)   = rsOut (λ ())
relayAdvRfw _ _ (raProd b _ _ a56)   = rsOut (λ ())
relayAdvRfw _ _ (raProd b _ _ a67)   = rsOut (λ ())
relayAdvRfw _ _ (raProd b _ _ a78)   = rsOut (λ ())
relayAdvRfw _ _ (raProd b _ _ a89)   = rsOut (λ ())

-- BASE — the guard is `⊥` at `initial` (the relay's driver is at `consuming blkA
-- cp0`), so the base case is vacuous.  Stated per leg because the accessor does not
-- reduce at a variable one
dnRfw-init : (l : TwoLegs) → DnRfw l initial
dnRfw-init legBD ()
dnRfw-init legCD ()

-- FRAME — the five components fixed
dnRfw-frame : (l : TwoLegs) (s s′ : SysState)
            → relayOf l s ≡ relayOf l s′
            → dnCSsOf l s ≡ dnCSsOf l s′
            → cellCSDn l s ≡ cellCSDn l s′
            → dnCScOf l s ≡ dnCScOf l s′
            → phOf l s ≡ phOf l s′
            → DnRfw l s → DnRfw l s′
dnRfw-frame l s s′ peq seq heq keq deq rw g′
  rewrite sym peq | sym seq | sym heq | sym keq | sym deq = rw g′

-- … and the OUT class: the successor leaves the guard, so the obligation is vacuous
dnRfw-out : (l : TwoLegs) (s s′ : SysState)
          → (RelayRfw (relayOf l s′) → ⊥) → DnRfw l s → DnRfw l s′
dnRfw-out l s s′ no rw g′ = ⊥-elim (no g′)

-- *** THE KEYSTONE — THE ENTERING STEP, AND IT IS FREE. ***  At the relay's own
-- `sendCSAwaitReply` hop (`pp1 → pp2`) the cone's LANDED `DnCsAwLand` (T6d, already
-- carried in `DnCsDrv`'s landing pair) puts the down CS server at `csWar`, which is
-- in `SrvPre` — so `ChanCS`'s `ccQui` hands over the cell and `ccPre` the client,
-- and every one of the record's ten fields is then either one of those two, a
-- `csWar`-vacuity, or the ORDER FACT read off `DrvCliD`'s `cp0` clause.
--
-- *** THIS LEMMA IS THE WHOLE OF §6g's POSTSCRIPT AS A PROOF: *** with a
-- `{pp3}`-only guard the entering step's server is `csMust`, where `SrvPre` is `⊥`
-- and NOTHING below would be available.  Moving the guard's left end back by one
-- sub-phase is what makes the object exist.
--
-- *** AND THAT NEGATIVE IS NOW MACHINE-CHECKED, WHICH IT WAS NOT WHEN THE LEMMA
-- LANDED (T11 review's I-3 — the round's headline was a NEGATIVE and a positive
-- proof at `pp2` does not establish it). ***
--
-- (F97  *** THE `{pp3}`-ONLY GUARD's OWN ENTERING STEP. ***)  restate this lemma at
--      the phase a `{pp3}`-only guard would enter — `relayOf l s′ ≡ producing b pp3`
--      — keeping every other hypothesis, including the `csWar` landing that is the
--      only position `ChanCS` can speak at.  Arity-preserving.
--      *** RED ***: `LiveDrvCSD.agda:2702.13-22: [UnequalTerms] _A ⊎ _B !=<
--      SrvRfw (SStep.coarsenCSs (dnCSsOf l s′)) … when checking that the inferred
--      type of an application _A ⊎ _B matches the expected type SrvRfw (…)`,
--      EXIT=42.  *** THE ERROR EXHIBITS THE GAP EXACTLY: *** at `pp3` the record's
--      own server region is `SrvRfw` = `{csWrf ht, csIdle}`, which does not admit
--      the `⊎`-shaped `pp2` region at all — so the ONE position the channel
--      invariant can hand over (`csWar` ∈ `SrvPre`) is OUTSIDE the region a
--      `{pp3}`-only guard would have to establish, and the establishment has nothing
--      to build from.  Reverted by string inversion, `git status` clean after.
--      Re-aiming note: F97 dies if `SrvRfw` is ever widened to `csWar` — which is
--      exactly what a successor tempted back to the narrow guard would try, and
--      what `dnRfw⇒leaf`'s `empty-arms` would then leave unrefuted.
dnRfw-enter : (l : TwoLegs) (s′ : SysState) (b : Block₃)
              -- the successor's phase: the hop LANDED at `pp2`
            → relayOf l s′ ≡ producing b pp2
              -- the cone's landing (T6d's `DnCsAwLand`, already carried)
            → SStep.coarsenCSs (dnCSsOf l s′) ≡ NS.csWar
              -- the hop's CHANNEL invariant (carried) …
            → CellPreQ (cellCSDn l s′)
            → CliAwt (dnCScC l s′)
              -- … and node D's coupling (carried), for the ORDER FACT
            → DrvCliD l s′
            → DnRfw l s′
dnRfw-enter l s′ b peq hwar hcell hcli cpl _ =
  mkDnRfwC
    -- the server: the landing IS the `pp2` region's left disjunct
    (subst (λ z → SrvAtRfw z (SStep.coarsenCSs (dnCSsOf l s′))) (sym peq)
           (inj₁ hwar))
    (cliAwt⇒reg (dnCScC l s′) hcli)
    (cellPreQ⇒rfw (cellCSDn l s′) hcell)
    -- the ORDER FACT: an awaiting client is not idle, and `DrvCliD`'s `cp0` clause
    -- says an idle client is what `cp0` forces
    (phase-arms (phOf l s′) refl)
    -- the three correlations are VACUOUS: a pre-region cell holds no responder
    -- payload, and `csWar` is neither `csMust` nor `csWrf` nor `csIdle`
    (λ har → ⊥-elim (arOnly-preQ-⊥ (cellCSDn l s′) hcell har))
    (λ hrf → ⊥-elim (rfwOnly-preQ-⊥ (cellCSDn l s′) hcell hrf))
    (λ _ → hcli , hcell)
    (λ hmu → ⊥-elim (war≢must (trans (sym hwar) hmu)))
    (λ ht hwf → ⊥-elim (war≢wrf ht (trans (sym hwar) hwf)))
    (λ _ hidl → ⊥-elim (war≢idle (trans (sym hwar) hidl)))
    -- (T11b) the two extra fields are vacuous here for the same reason as the three
    -- above: a pre-region cell holds no responder payload at all
    (λ hrf → ⊥-elim (rfwOnly-preQ-⊥ (cellCSDn l s′) hcell hrf))
    (λ har → ⊥-elim (arOnly-preQ-⊥ (cellCSDn l s′) hcell har))
  where
  -- `csWar` is none of the other three positions the fields' antecedents name.
  -- Stated at CONCRETE positions: at an abstract one the clash is not a pattern
  -- (measured: `[ShouldBeEmpty] NS.csWar ≡ q … refl is valid`)
  war≢must : NS.csWar ≡ NS.csMust → ⊥
  war≢must ()
  war≢wrf : (ht : Header × Tip) → NS.csWar ≡ NS.csWrf ht → ⊥
  war≢wrf ht ()
  war≢idle : NS.csWar ≡ NS.csIdle → ⊥
  war≢idle ()
  -- the phase dispatch: at `cp0` the coupling forces `ccIdle`, which contradicts
  -- `CliAwt`; every other phase is `⊤`
  phase-arms : (x : ConsPh) → phOf l s′ ≡ x → PhRfwD (phOf l s′)
  phase-arms cp0 hx =
    ⊥-elim (cliAwt-idle-⊥ (subst CliAwt (drvCliD-to0 l s′ cpl hx) hcli))
  phase-arms cp1 hx = subst PhRfwD (sym hx) tt
  phase-arms cp2 hx = subst PhRfwD (sym hx) tt
  phase-arms cp3 hx = subst PhRfwD (sym hx) tt
  phase-arms cp4 hx = subst PhRfwD (sym hx) tt
  phase-arms cp5 hx = subst PhRfwD (sym hx) tt
  phase-arms cp6 hx = subst PhRfwD (sym hx) tt

------------------------------------------------------------------------
-- §6i  (T11b) *** THE `{pp2, pp3}` RECORD's PRESERVATION CALCULUS — §5's shape at
-- the second guarded object, and the last piece of the `pp3` arm. ***
--
-- Read against §5, which is this calculus two fields and one INDEX short: `DnRfwC`
-- carries the RELAY's phase as its fifth index because field 1 is phase-indexed
-- (`SrvAtRfw`).  Everything else is §5 verbatim in SHAPE — six step classes, one
-- lift, the state-level wrappers — and the relay's own classes are §6h's
-- (`dnRfw-init`, `dnRfw-frame`, `dnRfw-out`, `dnRfw-enter`) plus the ONE in-guard
-- ADVANCE this section adds (`relayAdvRfw`'s `rsAdv`).
--
-- *** WHAT THE GUARD BUYS THE CLASSES, and it is why they are cheap. ***  Each class
-- that touches field 1 takes `RelayRfw rx` and dispatches it through
-- `rfwPhase-elim`, so `SrvAtRfw rx sa` — which does NOT reduce at an abstract `rx` —
-- reduces in each branch.  The "29-clause `SrvAtRfw` transport dispatch" the round-4
-- map priced is that ONE eleven-clause eliminator plus three four-line transports.
--
-- *** THE T11 REVIEW's I-5 "FIRST CHEAP WIN" IS REFUTED — DO NOT TAKE IT. ***  I-5
-- banked "make `SrvAtRfw`'s `pp2` clause `⊤` and read the region off the carried
-- `LiveDrvBF.DrvCp`" as an unmeasured −20-40 and named it T11b's first cheap win.
-- Traced against this calculus it is a NET COST, and the reason is the server's own
-- wire-send class: the `pp2` clause is what refutes `ssRB`, `ssIF` and `ssINF`
-- (whose payloads `CellRfw` does not admit, so their successors break field 3) AND
-- the `ssRF` row's source at `pp2`.  With the clause at `⊤` every one of those four
-- needs `DrvCp` threaded into the io classes plus an `rx` dispatch to know the
-- threading applies — more plumbing, not less, and a NEW coupling to a second
-- carried object in six classes instead of one.  *** The clause stays exactly as
-- landed, and its KEEP-IN-SYNC note with it. ***
--
-- *** AND TWO FIELDS GET NARROWER, not wider, for C-1's reason — the round-3 map's
-- own defence of their width is spent. ***  `CliRfwReg` now excludes `ccWdone` and
-- `ccTerm`, and `rwEmp`'s conclusion loses their two disjuncts.  The map defended
-- the width by "node D's `cdDone` hop lands the client at `ccWdone` and its own
-- write at `ccTerm`, and both are inside" — but `cdDone` fires at `cp5`, where the
-- carried token's `InCp03` is `⊥`, so the hop is REFUTED and both positions are
-- unreachable inside the guard.  *** The narrowing is what refutes the client's own
-- `csDone` WIRE-SEND, whose `MsgCSDone` payload is round 4's threat: *** field 3
-- does not admit it and must not (widening re-opens the leaf), so the row has to die
-- at its SOURCE, and `ccWdone ∉ CliRfwReg` is what kills it.  Round 4 looked for a
-- correlation; the region was enough.
--
-- *** DECLARED DEVIATION FROM THE REVIEW's PROBE SHAPE (C-1's four lemmas). ***  The
-- review probed `relayRfw-cases` + `pipeInv⇒inCp03-pp2` + `pipeInv⇒inCp03-pp3` + a
-- wrapper (≈45 lines).  Landed instead: `relayRfw-pre-⊥` / `relayRfw-fwd-⊥` (the two
-- refutations the level computation actually spends) + ONE `pipeInv⇒inCp03`, ≈28
-- lines and no `subst`.  Same content — the token's level is pinned by refuting the
-- OTHER two relay constraints rather than by naming the two phases — and
-- `pipeInv⇒sent-cp4` (`LiveRelayCS:462-469`) is still the shape of the level
-- elimination itself.
------------------------------------------------------------------------

-- *** §6i's OWN FALSIFICATIONS — two, one per novel family, and BOTH machine-check a
-- claim this section makes in prose. ***
--
-- (F101  *** THE I-5 "CHEAP WIN" IS A NET COST — TWO STAGES, as F92's re-aim was. ***)
--      weaken `SrvAtRfw`'s `pp2` clause to `⊤`, which is exactly what the T11
--      review's I-5 recommended.  Arity-preserving; the clause set is untouched.
--      (a) *** RED ***: `LiveDrvCSD.agda:2823.13-22: [UnequalTerms] _A ⊎ _B !=<
--          Level.Lift Level.zero U.⊤`, EXIT=42 — the KEYSTONE's own server field
--          goes first: `dnRfw-enter` hands over the landing as the region's LEFT
--          disjunct and a `⊤` clause does not admit an `⊎`.
--      (b) the same weakening with the keystone repaired to `tt` — *** RED ***:
--          `:2982.82-84: [UnequalTerms] (Level.Lift Level.zero U.⊤) !=< (sa ≡
--          NS.csWar ⊎ sa ≡ NS.csMust) … when checking that the expression hp has
--          type sa ≡ csWar ⊎ sa ≡ csMust`, EXIT=42 — and THIS is the substantive
--          one: `srvAtRfw-wrf⇒idle`'s `pp2` branch has nothing left to refute with,
--          so the server's own wire-send class loses the refutation of `ssRB`,
--          `ssIF`, `ssINF` and the `pp2`-sourced `ssRF`.  Both reverted by string
--          inversion, `git status` clean after each.
--      *** So the review's banked −20-40 is refuted by machine check, not by
--      argument, and the KEEP-IN-SYNC note above `SrvAtRfw` stays. ***
--
-- (F102  *** THE TOKEN IS LOAD-BEARING — C-1's phantom anatomy, machine-checked. ***)
--      replace `dnRfw-cliApi`'s token hypothesis `InCp03 x` by `PhRfwD x` — the
--      record's OWN field 4, i.e. the fact round 4 believed was the phase datum in
--      play.  Arity-preserving.  *** RED ***: `:3121.58-60: [UnequalTerms]
--      (Level.Lift Level.zero U.⊤) !=< ⊥ … when checking that the expression tk has
--      type ⊥`, EXIT=42 — at the `cdBF45` clause, whose source `cp4` field 4 admits
--      (`PhRfwD cp4 = ⊤`) and the token does not (`InCp03 cp4 = ⊥`).  `cdDone`'s
--      `cp5` fails the same way one clause later.  *** So field 4 CANNOT do the
--      api class's work and the carried token can: the decoupling is not a
--      restatement of the order fact. ***  Reverted by string inversion.

-- the guard's own two-way dispatch, as an ELIMINATOR.  Everything the classes want
-- from `RelayRfw` is "the relay's phase is one of the two", and taking the motive as
-- a parameter is what lets `SrvAtRfw` reduce inside each branch without a `subst`
rfwPhase-elim : (P : CPPh → Set) (rx : CPPh) → RelayRfw rx
              → ((b : Block₃) → P (producing b pp2))
              → ((b : Block₃) → P (producing b pp3))
              → P rx
rfwPhase-elim P (consuming b y)   () _  _
rfwPhase-elim P (producing b pp0) () _  _
rfwPhase-elim P (producing b pp1) () _  _
rfwPhase-elim P (producing b pp2) _  h2 _  = h2 b
rfwPhase-elim P (producing b pp3) _  _  h3 = h3 b
rfwPhase-elim P (producing b pp4) () _  _
rfwPhase-elim P (producing b pp5) () _  _
rfwPhase-elim P (producing b pp6) () _  _
rfwPhase-elim P (producing b pp7) () _  _
rfwPhase-elim P (producing b pp8) () _  _
rfwPhase-elim P (producing b pp9) () _  _

-- *** THE TOKEN PROJECTION — C-1's decoupling, in the two refutations it needs. ***
-- The guard is `⊥` at every phase `RelayPre` or `RelayFwd` admits, so a carried
-- `PipeInv` can only be at `L2`, whose D-consumer constraint IS `InCp03`
relayRfw-pre-⊥ : (x : CPPh) → RelayRfw x → RelayPre x → ⊥
relayRfw-pre-⊥ (consuming b y)   () _
relayRfw-pre-⊥ (producing b pp0) () _
relayRfw-pre-⊥ (producing b pp1) () _
relayRfw-pre-⊥ (producing b pp2) _  ()
relayRfw-pre-⊥ (producing b pp3) _  ()
relayRfw-pre-⊥ (producing b pp4) () _
relayRfw-pre-⊥ (producing b pp5) () _
relayRfw-pre-⊥ (producing b pp6) () _
relayRfw-pre-⊥ (producing b pp7) () _
relayRfw-pre-⊥ (producing b pp8) () _
relayRfw-pre-⊥ (producing b pp9) () _

relayRfw-fwd-⊥ : (x : CPPh) → RelayRfw x → RelayFwd x → ⊥
relayRfw-fwd-⊥ (consuming b y)   () _
relayRfw-fwd-⊥ (producing b pp0) () _
relayRfw-fwd-⊥ (producing b pp1) () _
relayRfw-fwd-⊥ (producing b pp2) _  ()
relayRfw-fwd-⊥ (producing b pp3) _  ()
relayRfw-fwd-⊥ (producing b pp4) () _
relayRfw-fwd-⊥ (producing b pp5) () _
relayRfw-fwd-⊥ (producing b pp6) () _
relayRfw-fwd-⊥ (producing b pp7) () _
relayRfw-fwd-⊥ (producing b pp8) () _
relayRfw-fwd-⊥ (producing b pp9) () _

-- … and the projection itself: `pipeInv⇒sent-cp4`'s five-clause level elimination,
-- at the guard instead of at `consuming _ cp4`.  *** THIS IS THE WHOLE OF C-1: ***
-- node D's `{cp0 … cp3}` is DERIVED at every state in the record's own guard, so it
-- is not a field, has nothing to preserve, and needs no second carried object
pipeInv⇒inCp03 : (l : TwoLegs) (s : SysState)
               → RelayRfw (relayOf l s) → PipeInv l s → InCp03 (phOf l s)
pipeInv⇒inCp03 l s g (L0 , _ , hr , _)  = ⊥-elim (relayRfw-pre-⊥ _ g hr)
pipeInv⇒inCp03 l s g (L1 , _ , hr , _)  = ⊥-elim (relayRfw-pre-⊥ _ g hr)
pipeInv⇒inCp03 l s g (L2 , _ , _  , hc) = hc
pipeInv⇒inCp03 l s g (L3 , _ , hr , _)  = ⊥-elim (relayRfw-fwd-⊥ _ g hr)
pipeInv⇒inCp03 l s g (L4 , _ , hr , _)  = ⊥-elim (relayRfw-fwd-⊥ _ g hr)

-- the server's ONE admitted wire-send inside the guard — `ssRF`'s row, `csWrf ht →
-- csIdle`.  At `pp2` the SOURCE is outside the region (the row belongs to `pp3`), at
-- `pp3` the target IS `SrvRfw`'s own `csIdle`
srvAtRfw-wrf⇒idle : (rx : CPPh) (sa : NS.CSsPos) → RelayRfw rx
                  → (ht : Header × Tip) → sa ≡ NS.csWrf ht
                  → SrvAtRfw rx sa → SrvAtRfw rx NS.csIdle
srvAtRfw-wrf⇒idle rx sa g ht eq =
  rfwPhase-elim (λ z → SrvAtRfw z sa → SrvAtRfw z NS.csIdle) rx g
    (λ _ hp → ⊥-elim (wrf-not (subst (λ q → (q ≡ NS.csWar) ⊎ (q ≡ NS.csMust)) eq hp)))
    (λ _ _  → tt)
  where
  wrf-not : (NS.csWrf ht ≡ NS.csWar) ⊎ (NS.csWrf ht ≡ NS.csMust) → ⊥
  wrf-not (inj₁ ())
  wrf-not (inj₂ ())

-- … and the region's own io step INSIDE `pp2` — `ssAR`'s row, `csWar → csMust`.  At
-- `pp3` the SOURCE is outside `SrvRfw`, which is the mirror of the lemma above
srvAtRfw-war⇒must : (rx : CPPh) (sa : NS.CSsPos) → RelayRfw rx
                  → sa ≡ NS.csWar
                  → SrvAtRfw rx sa → SrvAtRfw rx NS.csMust
srvAtRfw-war⇒must rx sa g eq =
  rfwPhase-elim (λ z → SrvAtRfw z sa → SrvAtRfw z NS.csMust) rx g
    (λ _ _  → inj₂ refl)
    (λ _ hp → ⊥-elim (subst SrvRfw eq hp))

-- … and the three wire-send rows the region admits at NEITHER phase.  Their sources
-- are the server's other three `csW*` positions, and the payloads they would put in
-- the cell are exactly the ones `CellRfw` does not admit — so without this the
-- successor's field 3 is unprovable, which is why the `pp2` clause is load-bearing
srvAtRfw-off : (rx : CPPh) (sa : NS.CSsPos) → RelayRfw rx
             → (sa ≡ NS.csWar → ⊥) → (sa ≡ NS.csMust → ⊥) → (SrvRfw sa → ⊥)
             → SrvAtRfw rx sa → ⊥
srvAtRfw-off rx sa g nw nm nr =
  rfwPhase-elim (λ z → SrvAtRfw z sa → ⊥) rx g
    (λ _ → λ { (inj₁ h) → nw h ; (inj₂ h) → nm h })
    (λ _ → nr)

-- inside `CellRfw` a FULL cell holds one of the two responder payloads the region
-- names and nothing else — `cellFresh-full`'s shape at the four-armed region
cellRfw-full : (y : Payload) → CellRfw (SM.full y)
             → ArOnly (SM.full y) ⊎ RfwOnly (SM.full y)
cellRfw-full y (inj₁ ())
cellRfw-full y (inj₂ (inj₁ (_ , ())))
cellRfw-full y (inj₂ (inj₂ (inj₁ har))) = inj₁ har
cellRfw-full y (inj₂ (inj₂ (inj₂ hrf))) = inj₂ hrf

-- … so any OTHER ChainSync message in a full cell is refuted.  `reqOnly-not`'s shape
-- at TWO admitted messages instead of one: the caller supplies both clashes for its
-- own row, and every io READ class but the two rollforward arms spends this
cellRfw-not : (t : Time) (md : Mode) (ln : Length) (mc : MessageChainSync)
            → (mc ≡ MsgCSAwaitReply → ⊥)
            → ((h : Header) (tp : Tip) → mc ≡ MsgCSRollForward h tp → ⊥)
            → CellRfw (SM.full (t , md , ln , chainSync mc)) → ⊥
cellRfw-not t md ln mc noAr noRf h with cellRfw-full _ h
... | inj₁ (_ , _ , _ , refl)           = noAr refl
... | inj₂ (hh , tp , _ , _ , _ , refl) = noRf hh tp refl

-- the region's two responder payloads, as the cell arms the two admitted server
-- wire-sends ESTABLISH
arOnly-ar : ArOnly (SM.full arPayload)
arOnly-ar = _ , _ , _ , refl

rfwOnly-rf : (h : Header) (tp : Tip) → RfwOnly (SM.full (rfPayload h tp))
rfwOnly-rf h tp = h , tp , _ , _ , _ , refl

-- … and each excludes the other's message, which is what makes the two correlations
-- vacuous at each other's write
arOnly-rf-⊥ : (h : Header) (tp : Tip) → ArOnly (SM.full (rfPayload h tp)) → ⊥
arOnly-rf-⊥ h tp (_ , _ , _ , ())

rfwOnly-ar-⊥ : RfwOnly (SM.full arPayload) → ⊥
rfwOnly-ar-⊥ (_ , _ , _ , _ , _ , ())

-- a client at `ccArf ht` is neither AWAITING nor at `ccMust` — the ONE refutation
-- node D's own `recvCSRollforward` hop spends, at four of the record's fields
awtMust-arf-⊥ : (ht : Header × Tip)
              → CliAwt (NS.ccArf ht) ⊎ (NS.ccArf ht ≡ NS.ccMust) → ⊥
awtMust-arf-⊥ ht (inj₁ ())
awtMust-arf-⊥ ht (inj₂ ())

-- the two positions an unread await-reply pins the server to are neither `csWar`
-- (its own source, already left) nor `csIdle` — this is what field 10 buys the
-- client's own read of that message, whose successor `ccMust` fields 5c and 8 would
-- otherwise have no way to answer
arS-not : (sa : NS.CSsPos)
        → (sa ≡ NS.csMust) ⊎ (Σ[ ht ∈ Header × Tip ] sa ≡ NS.csWrf ht)
        → (sa ≡ NS.csWar → ⊥) × (sa ≡ NS.csIdle → ⊥)
arS-not sa (inj₁ refl)        = (λ ()) , (λ ())
arS-not sa (inj₂ (ht , refl)) = (λ ()) , (λ ())

-- the two BlockFetch carrying hops move node D's PHASE and nothing else this record
-- mentions, and both land inside field 4 — so the record transports and only the
-- phase field is rebuilt
dnRfwC-phase : (rx : CPPh) (sa : NS.CSsPos) (ph : SM.CopyPhase) (ca : NS.CScPos)
               (x x′ : ConsPh) → PhRfwD x′
             → DnRfwC sa ph ca x rx → DnRfwC sa ph ca x′ rx
dnRfwC-phase rx sa ph ca x x′ hx rw =
  mkDnRfwC (rwSrv rw) (rwCli rw) (rwCell rw) hx (rwAr rw) (rwRfw rw)
           (rwWar rw) (rwMst rw) (rwWrf rw) (rwEmp rw) (rwRfwS rw) (rwArS rw)

-- transport the core along equalities of its FIVE components — what every frame and
-- every fixity hypothesis hands over
dnRfwC-cong : (sa sa′ : NS.CSsPos) (ph ph′ : SM.CopyPhase) (ca ca′ : NS.CScPos)
              (x x′ : ConsPh) (rx rx′ : CPPh)
            → sa ≡ sa′ → ph ≡ ph′ → ca ≡ ca′ → x ≡ x′ → rx ≡ rx′
            → DnRfwC sa ph ca x rx → DnRfwC sa′ ph′ ca′ x′ rx′
dnRfwC-cong sa _ ph _ ca _ x _ rx _ refl refl refl refl refl rw = rw

-- *** THE LIFT. ***  Every class but the relay's own advance fixes the relay's
-- phase, so the guard transports BACKWARDS along the step and the guarded object's
-- preservation is exactly the core's
dnRfw-lift : (l : TwoLegs) (s s′ : SysState)
           → relayOf l s ≡ relayOf l s′
           → (DnRfwC (SStep.coarsenCSs (dnCSsOf l s)) (cellCSDn l s)
                     (dnCScC l s) (phOf l s) (relayOf l s)
              → DnRfwC (SStep.coarsenCSs (dnCSsOf l s′)) (cellCSDn l s′)
                       (dnCScC l s′) (phOf l s′) (relayOf l s′))
           → DnRfw l s → DnRfw l s′
dnRfw-lift l s s′ peq step rw g′ = step (rw (subst RelayRfw (sym peq) g′))

-- (1) *** NODE D's api CLASS — the ONE class the carried token enters. ***  The
-- relay's server, the hop's cell and the relay's phase are all fixed; only node D's
-- client and its own phase move.  THREE rows survive — `cdRecvF`, whose successor
-- `ccIdle` refutes every correlation's CONSEQUENT so each is closed by refuting its
-- ANTECEDENT from the SOURCE's own field, and the two BlockFetch carrying hops
-- `cdBF23`/`cdBF34`.  `cdReq` is refuted by field 4 (its source is `cp0`), and
-- *** `cdBF45` and `cdDone` by the TOKEN: their sources are `cp4` and `cp5`, where
-- `InCp03` is `⊥`. ***  Those two are C-1's decoupling doing its entire job —
-- `cdDone` is round 4's threat and no `BFFresh` conjunct appears anywhere
dnRfw-cliApi : (rx : CPPh) (sa : NS.CSsPos) (ph : SM.CopyPhase) (ca ca′ : NS.CScPos)
               (x x′ : ConsPh)
             → InCp03 x
             → CliDrvAdj ca x ca′ x′
             → DnRfwC sa ph ca x rx → DnRfwC sa ph ca′ x′ rx
dnRfw-cliApi rx sa ph _ _ _ _ tk cdReq        rw = ⊥-elim (rwPh rw)
dnRfw-cliApi rx sa ph _ _ _ _ tk (cdRecvF ht) rw =
  mkDnRfwC (rwSrv rw) tt (rwCell rw) tt
    (λ har     → ⊥-elim (rwAr rw har))
    (λ hrf     → ⊥-elim (awtMust-arf-⊥ ht (rwRfw rw hrf)))
    (λ hwr     → ⊥-elim (proj₁ (rwWar rw hwr)))
    (λ hmu     → ⊥-elim (awtMust-arf-⊥ ht (rwMst rw hmu)))
    (λ ht′ hwf → ⊥-elim (awtMust-arf-⊥ ht (rwWrf rw ht′ hwf)))
    (λ _ _     → inj₂ refl)
    (λ hrf     → ⊥-elim (awtMust-arf-⊥ ht (rwRfw rw hrf)))
    (λ har     → ⊥-elim (rwAr rw har))
dnRfw-cliApi rx sa ph _ _ _ _ tk (cdBF23 ca) rw = dnRfwC-phase _ _ _ _ _ _ tt rw
dnRfw-cliApi rx sa ph _ _ _ _ tk (cdBF34 ca) rw = dnRfwC-phase _ _ _ _ _ _ tt rw
dnRfw-cliApi rx sa ph _ _ _ _ tk (cdBF45 ca) rw = ⊥-elim tk
dnRfw-cliApi rx sa ph _ _ _ _ tk cdDone      rw = ⊥-elim tk

-- (2) *** THE io FILL BY THE SERVER — the class that carries the two correlations'
-- ESTABLISHMENT, and the one that needs the phase index. ***  `ssRF` writes the
-- rollforward (field 5b off the source's field 7, field 9 free at `csIdle`), `ssAR`
-- writes the await-reply (fields 5/6 off the source's field 5c, field 10 free at
-- `csMust`), and the other three rows are refuted by field 1 at BOTH phases
dnRfw-srvSend : (rx : CPPh) (sa sa′ : NS.CSsPos) (y : Payload) (ca : NS.CScPos)
                (x : ConsPh)
              → RelayRfw rx
              → SrvSendAdj sa y sa′
              → DnRfwC sa SM.empty ca x rx → DnRfwC sa′ (SM.full y) ca x rx
dnRfw-srvSend rx _ _ _ ca x g (ssRF h tp) rw =
  mkDnRfwC (srvAtRfw-wrf⇒idle rx _ g (h , tp) refl (rwSrv rw))
           (rwCli rw)
           (inj₂ (inj₂ (inj₂ (rfwOnly-rf h tp))))
           (rwPh rw)
           (λ har → ⊥-elim (arOnly-rf-⊥ h tp har))
           (λ _   → rwWrf rw (h , tp) refl)
           (λ ())
           (λ ())
           (λ _ ())
           (λ hq _ → ⊥-elim (preQ-full-⊥ _ hq))
           (λ _   → refl)
           (λ har → ⊥-elim (arOnly-rf-⊥ h tp har))
dnRfw-srvSend rx _ _ _ ca x g ssAR rw =
  mkDnRfwC (srvAtRfw-war⇒must rx _ g refl (rwSrv rw))
           (rwCli rw)
           (inj₂ (inj₂ (inj₁ arOnly-ar)))
           (rwPh rw)
           (λ _   → proj₁ (rwWar rw refl))
           (λ hrf → ⊥-elim (rfwOnly-ar-⊥ hrf))
           (λ ())
           (λ _   → inj₁ (proj₁ (rwWar rw refl)))
           (λ _ ())
           (λ hq _ → ⊥-elim (preQ-full-⊥ _ hq))
           (λ hrf → ⊥-elim (rfwOnly-ar-⊥ hrf))
           (λ _   → inj₁ refl)
dnRfw-srvSend rx _ _ _ ca x g (ssRB pt tp) rw =
  ⊥-elim (srvAtRfw-off rx _ g (λ ()) (λ ()) (λ ()) (rwSrv rw))
dnRfw-srvSend rx _ _ _ ca x g (ssIF pt tp) rw =
  ⊥-elim (srvAtRfw-off rx _ g (λ ()) (λ ()) (λ ()) (rwSrv rw))
dnRfw-srvSend rx _ _ _ ca x g (ssINF tp)   rw =
  ⊥-elim (srvAtRfw-off rx _ g (λ ()) (λ ()) (λ ()) (rwSrv rw))

-- (3) THE io FILL BY THE CLIENT — all three rows refuted by field 2 alone.  *** The
-- THIRD one is round 4's threat and it dies HERE: *** `csDone`'s source `ccWdone` is
-- outside the narrowed client region, so the `MsgCSDone` it would put in the cell
-- never reaches field 3
dnRfw-cliSend : (rx : CPPh) (sa : NS.CSsPos) (y : Payload) (ca ca′ : NS.CScPos)
                (x : ConsPh)
              → CliSendAdj ca y ca′
              → DnRfwC sa SM.empty ca x rx → DnRfwC sa (SM.full y) ca′ x rx
dnRfw-cliSend rx sa _ _ _ x csReq    rw = ⊥-elim (rwCli rw)
dnRfw-cliSend rx sa _ _ _ x (csFI _) rw = ⊥-elim (rwCli rw)
dnRfw-cliSend rx sa _ _ _ x csDone   rw = ⊥-elim (rwCli rw)

-- (4) THE SERVER's WIRE-READ — all three rows refuted by field 3: every one of them
-- needs an INITIATOR message in the cell, and the region admits only the two
-- responder payloads
dnRfw-srvRead : (rx : CPPh) (sa sa′ : NS.CSsPos) (y : Payload) (ca : NS.CScPos)
                (x : ConsPh)
              → SrvReadAdj sa y sa′
              → DnRfwC sa (SM.full y) ca x rx → DnRfwC sa′ (SM.draining y) ca x rx
dnRfw-srvRead rx _ _ _ ca x srReq    rw =
  ⊥-elim (cellRfw-not _ _ _ _ (λ ()) (λ _ _ ()) (rwCell rw))
dnRfw-srvRead rx _ _ _ ca x (srFI _) rw =
  ⊥-elim (cellRfw-not _ _ _ _ (λ ()) (λ _ _ ()) (rwCell rw))
dnRfw-srvRead rx _ _ _ ca x srDone   rw =
  ⊥-elim (cellRfw-not _ _ _ _ (λ ()) (λ _ _ ()) (rwCell rw))

-- the client's read of an unread ROLLFORWARD, shared by `crRF` and `crMRF`: the two
-- rows differ only in the SOURCE position, which no field below mentions, and the
-- successor `ccArf (h , tp)` is outside `CliAwt` at both — so fields 5c/6/7 are
-- closed by field 9's `csIdle`, and field 8 is FREE at exactly this step (`ccArf` is
-- its first disjunct)
rfwRead : (rx : CPPh) (sa : NS.CSsPos) (t : Time) (md : Mode) (ln : Length)
          (h : Header) (tp : Tip) (ca : NS.CScPos) (x : ConsPh)
        → DnRfwC sa (SM.full (t , md , ln , chainSync (MsgCSRollForward h tp))) ca x rx
        → DnRfwC sa (SM.draining (t , md , ln , chainSync (MsgCSRollForward h tp)))
                 (NS.ccArf (h , tp)) x rx
rfwRead rx sa t md ln h tp ca x rw =
  mkDnRfwC (rwSrv rw) tt (inj₂ (inj₁ (_ , refl))) (rwPh rw)
    (λ har → ⊥-elim (arOnly-preQ-⊥ _ (inj₂ (_ , refl)) har))
    (λ hrf → ⊥-elim (rfwOnly-preQ-⊥ _ (inj₂ (_ , refl)) hrf))
    (λ hwr → ⊥-elim (idle≢war (trans (sym (rwRfwS rw src)) hwr)))
    (λ hmu → ⊥-elim (idle≢must (trans (sym (rwRfwS rw src)) hmu)))
    (λ ht′ hwf → ⊥-elim (idle≢wrf ht′ (trans (sym (rwRfwS rw src)) hwf)))
    (λ _ _ → inj₁ ((h , tp) , refl))
    (λ hrf → ⊥-elim (rfwOnly-preQ-⊥ _ (inj₂ (_ , refl)) hrf))
    (λ har → ⊥-elim (arOnly-preQ-⊥ _ (inj₂ (_ , refl)) har))
  where
  src : RfwOnly (SM.full (t , md , ln , chainSync (MsgCSRollForward h tp)))
  src = h , tp , t , md , ln , refl
  idle≢war : NS.csIdle ≡ NS.csWar → ⊥
  idle≢war ()
  idle≢must : NS.csIdle ≡ NS.csMust → ⊥
  idle≢must ()
  idle≢wrf : (ht : Header × Tip) → NS.csIdle ≡ NS.csWrf ht → ⊥
  idle≢wrf ht ()

-- (5) *** THE CLIENT's WIRE-READ — the class fields 9 and 10 EXIST FOR. ***  Four of
-- the seven rows carry a message the region excludes (field 3); the three that
-- survive all move the client OUT of `CliAwt`, so fields 5c/6/7 can only be
-- preserved by refuting their ANTECEDENTS — and what refutes them is the
-- cell⇒server correlation the source carries: an unread rollforward pins the server
-- at `csIdle` (field 9, the two `ccArf` arms), an unread await-reply pins it at
-- `csMust`-or-`csWrf` (field 10, the `ccMust` arm)
dnRfw-cliRead : (rx : CPPh) (sa : NS.CSsPos) (y : Payload) (ca ca′ : NS.CScPos)
                (x : ConsPh)
              → CliReadAdj ca y ca′
              → DnRfwC sa (SM.full y) ca x rx → DnRfwC sa (SM.draining y) ca′ x rx
dnRfw-cliRead rx sa _ _ _ x (crRF h tp)  rw = rfwRead rx sa _ _ _ h tp _ x rw
dnRfw-cliRead rx sa _ _ _ x (crMRF h tp) rw = rfwRead rx sa _ _ _ h tp _ x rw
dnRfw-cliRead rx sa _ _ _ x crAR         rw =
  mkDnRfwC (rwSrv rw) tt (inj₂ (inj₁ (_ , refl))) (rwPh rw)
    (λ har → ⊥-elim (arOnly-preQ-⊥ _ (inj₂ (_ , refl)) har))
    (λ hrf → ⊥-elim (rfwOnly-preQ-⊥ _ (inj₂ (_ , refl)) hrf))
    (λ hwr → ⊥-elim (proj₁ (arS-not _ (rwArS rw (_ , _ , _ , refl))) hwr))
    (λ _    → inj₂ refl)
    (λ _ _  → inj₂ refl)
    (λ _ hidl → ⊥-elim (proj₂ (arS-not _ (rwArS rw (_ , _ , _ , refl))) hidl))
    (λ hrf → ⊥-elim (rfwOnly-preQ-⊥ _ (inj₂ (_ , refl)) hrf))
    (λ har → ⊥-elim (arOnly-preQ-⊥ _ (inj₂ (_ , refl)) har))
dnRfw-cliRead rx sa _ _ _ x (crRB _ _)  rw =
  ⊥-elim (cellRfw-not _ _ _ _ (λ ()) (λ _ _ ()) (rwCell rw))
dnRfw-cliRead rx sa _ _ _ x (crMRB _ _) rw =
  ⊥-elim (cellRfw-not _ _ _ _ (λ ()) (λ _ _ ()) (rwCell rw))
dnRfw-cliRead rx sa _ _ _ x (crIF _ _)  rw =
  ⊥-elim (cellRfw-not _ _ _ _ (λ ()) (λ _ _ ()) (rwCell rw))
dnRfw-cliRead rx sa _ _ _ x (crINF _)   rw =
  ⊥-elim (cellRfw-not _ _ _ _ (λ ()) (λ _ _ ()) (rwCell rw))

-- (6) *** THE MEDIUM's OWN DRAIN τ — the class field 8's GENERALISED antecedent
-- exists for. ***  `draining y → empty` keeps every position, and with the antecedent
-- at `CellPreQ` rather than `ph ≡ empty` the drain is a pure TRANSPORT: without it
-- the class would have to invent the client's position out of nothing
dnRfw-drain : (rx : CPPh) (sa : NS.CSsPos) (y : Payload) (ca : NS.CScPos) (x : ConsPh)
            → DnRfwC sa (SM.draining y) ca x rx → DnRfwC sa SM.empty ca x rx
dnRfw-drain rx sa y ca x rw =
  mkDnRfwC (rwSrv rw) (rwCli rw) (inj₁ refl) (rwPh rw)
    (λ har → ⊥-elim (arOnly-preQ-⊥ _ (inj₁ refl) har))
    (λ hrf → ⊥-elim (rfwOnly-preQ-⊥ _ (inj₁ refl) hrf))
    (λ hwr → proj₁ (rwWar rw hwr) , inj₁ refl)
    (rwMst rw)
    (rwWrf rw)
    (λ _ hidl → rwEmp rw (inj₂ (y , refl)) hidl)
    (λ hrf → ⊥-elim (rfwOnly-preQ-⊥ _ (inj₁ refl) hrf))
    (λ har → ⊥-elim (arOnly-preQ-⊥ _ (inj₁ refl) har))

-- *** (7) THE RELAY's ONE IN-GUARD ADVANCE — `relayAdvRfw`'s `rsAdv`, and the ONE
-- class that consumes the `pp3` CONE LANDING. ***  At the relay's own
-- `sendCSRollForward` sync (`pp2 → pp3`) the cell, node D's client and node D's
-- phase are all fixed and only the down CS server moves; the landing says WHERE, and
-- the source's field 1 — the `pp2` REGION — is what supplies the client fact field 7
-- needs at the successor.  *** The landing arrives already-APPLIED, as `DnCsAwLand`
-- does at the entering step: the carry (`LiveLegApiCone.DnCsRfwLand`) applies it. ***
dnRfw-relayAdv : (b : Block₃) (sa sa′ : NS.CSsPos) (ph : SM.CopyPhase)
                 (ca : NS.CScPos) (x : ConsPh) (ht : Header × Tip)
               → sa′ ≡ NS.csWrf ht
               → DnRfwC sa ph ca x (producing b pp2)
               → DnRfwC sa′ ph ca x (producing b pp3)
dnRfw-relayAdv b sa _ ph ca x ht refl rw =
  mkDnRfwC tt (rwCli rw) (rwCell rw) (rwPh rw) (rwAr rw) (rwRfw rw)
    (λ ()) (λ ()) (λ _ _ → cliFact) (λ _ ())
    (λ hrf → ⊥-elim (norf hrf))
    (λ _ → inj₂ (ht , refl))
  where
  -- the source server is at ONE of the `pp2` region's two ends, and each end carries
  -- the client fact the `csWrf` correlation wants
  cliFact : CliAwt ca ⊎ (ca ≡ NS.ccMust)
  cliFact with rwSrv rw
  ... | inj₁ hwar  = inj₁ (proj₁ (rwWar rw hwar))
  ... | inj₂ hmust = rwMst rw hmust
  -- … and an unread rollforward at the SOURCE would pin the same server at `csIdle`,
  -- which the region excludes: the arm is vacuous
  norf : RfwOnly ph → ⊥
  norf hrf with rwSrv rw
  ... | inj₁ hwar  = war-idle (trans (sym hwar) (rwRfwS rw hrf))
    where
    war-idle : NS.csWar ≡ NS.csIdle → ⊥
    war-idle ()
  ... | inj₂ hmust = must-idle (trans (sym hmust) (rwRfwS rw hrf))
    where
    must-idle : NS.csMust ≡ NS.csIdle → ⊥
    must-idle ()

------------------------------------------------------------------------
-- §6i(b)  THE STATE-LEVEL WRAPPERS — §5b's eight, at five components instead of
-- four.  The guard travels backwards through `dnRfw-lift` in all but the last.
------------------------------------------------------------------------

-- NODE D's api SYNC, at the state's slots.  *** The token is a PARAMETER, not a
-- field: *** the caller reads it off the carried `PipeInv` at the SOURCE with
-- `pipeInv⇒inCp03`, which is what makes the api class single-object
dnRfw-nodeDApi : (l : TwoLegs) (s s′ : SysState)
               → relayOf l s ≡ relayOf l s′
               → dnCSsOf l s ≡ dnCSsOf l s′
               → cellCSDn l s ≡ cellCSDn l s′
               → InCp03 (phOf l s)
               → CliDrvAdj (dnCScC l s) (phOf l s) (dnCScC l s′) (phOf l s′)
               → DnRfw l s → DnRfw l s′
dnRfw-nodeDApi l s s′ peq seq heq tk adj =
  dnRfw-lift l s s′ peq
    (λ rw → dnRfw-cliApi _ _ _ _ _ _ _ tk adj
              (dnRfwC-cong _ _ _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) heq
                           refl refl peq rw))

-- the SERVER's io FILL, at the state's slots (the cell's two phases come from the
-- medium's banked key lemmas)
dnRfw-srvSendS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
               → relayOf l s ≡ relayOf l s′
               → cellCSDn l s ≡ SM.empty → cellCSDn l s′ ≡ SM.full y
               → dnCScOf l s ≡ dnCScOf l s′ → phOf l s ≡ phOf l s′
               → SrvSendAdj (SStep.coarsenCSs (dnCSsOf l s)) y
                            (SStep.coarsenCSs (dnCSsOf l s′))
               → DnRfw l s → DnRfw l s′
-- *** THE ONE WRAPPER THAT CANNOT GO THROUGH `dnRfw-lift`, and the reason is worth
-- a line: *** the class needs the GUARD as well as the core, and the lift's `step`
-- argument only ever sees the core.  So the guard is transported backwards HERE, at
-- the wrapper, and used twice
dnRfw-srvSendS l s s′ y peq he he′ keq deq adj rw g′ =
  dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl (sym he′) (cong coarsenCSc keq) deq peq
    (dnRfw-srvSend (relayOf l s) _ _ y (dnCScC l s) (phOf l s) g adj
      (dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl he refl refl refl (rw g)))
  where
  g : RelayRfw (relayOf l s)
  g = subst RelayRfw (sym peq) g′

-- … the CLIENT's io FILL
dnRfw-cliSendS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
               → relayOf l s ≡ relayOf l s′
               → cellCSDn l s ≡ SM.empty → cellCSDn l s′ ≡ SM.full y
               → dnCSsOf l s ≡ dnCSsOf l s′ → phOf l s ≡ phOf l s′
               → CliSendAdj (dnCScC l s) y (dnCScC l s′)
               → DnRfw l s → DnRfw l s′
dnRfw-cliSendS l s s′ y peq he he′ seq deq adj =
  dnRfw-lift l s s′ peq
    (λ rw → dnRfwC-cong _ _ _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) (sym he′)
                        refl deq peq
              (dnRfw-cliSend (relayOf l s) _ y _ _ (phOf l s) adj
                (dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl he refl refl refl rw)))

-- … the SERVER's io READ
dnRfw-srvReadS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
               → relayOf l s ≡ relayOf l s′
               → cellCSDn l s ≡ SM.full y → cellCSDn l s′ ≡ SM.draining y
               → dnCScOf l s ≡ dnCScOf l s′ → phOf l s ≡ phOf l s′
               → SrvReadAdj (SStep.coarsenCSs (dnCSsOf l s)) y
                            (SStep.coarsenCSs (dnCSsOf l s′))
               → DnRfw l s → DnRfw l s′
dnRfw-srvReadS l s s′ y peq hf he′ keq deq adj =
  dnRfw-lift l s s′ peq
    (λ rw → dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl (sym he′) (cong coarsenCSc keq)
                        deq peq
              (dnRfw-srvRead (relayOf l s) _ _ y _ (phOf l s) adj
                (dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl hf refl refl refl rw)))

-- … the CLIENT's io READ
dnRfw-cliReadS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
               → relayOf l s ≡ relayOf l s′
               → cellCSDn l s ≡ SM.full y → cellCSDn l s′ ≡ SM.draining y
               → dnCSsOf l s ≡ dnCSsOf l s′ → phOf l s ≡ phOf l s′
               → CliReadAdj (dnCScC l s) y (dnCScC l s′)
               → DnRfw l s → DnRfw l s′
dnRfw-cliReadS l s s′ y peq hf he′ seq deq adj =
  dnRfw-lift l s s′ peq
    (λ rw → dnRfwC-cong _ _ _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) (sym he′)
                        refl deq peq
              (dnRfw-cliRead (relayOf l s) _ y _ _ (phOf l s) adj
                (dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl hf refl refl refl rw)))

-- … and the medium's DRAIN τ
dnRfw-drainS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
             → relayOf l s ≡ relayOf l s′
             → cellCSDn l s ≡ SM.draining y → cellCSDn l s′ ≡ SM.empty
             → dnCSsOf l s ≡ dnCSsOf l s′
             → dnCScOf l s ≡ dnCScOf l s′ → phOf l s ≡ phOf l s′
             → DnRfw l s → DnRfw l s′
dnRfw-drainS l s s′ y peq hd he′ seq keq deq =
  dnRfw-lift l s s′ peq
    (λ rw → dnRfwC-cong _ _ _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) (sym he′)
                        (cong coarsenCSc keq) deq peq
              (dnRfw-drain (relayOf l s) _ y _ (phOf l s)
                (dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl hd refl refl refl rw)))

-- … and the relay's own in-guard ADVANCE, which is the ONE wrapper that is not a
-- lift: the guard moves with the step, so it is supplied at the SOURCE from the
-- arm's own phase equation rather than transported backwards
dnRfw-relayAdvS : (l : TwoLegs) (s s′ : SysState) (b : Block₃) (ht : Header × Tip)
                → relayOf l s ≡ producing b pp2
                → relayOf l s′ ≡ producing b pp3
                → SStep.coarsenCSs (dnCSsOf l s′) ≡ NS.csWrf ht
                → cellCSDn l s ≡ cellCSDn l s′
                → dnCScOf l s ≡ dnCScOf l s′
                → phOf l s ≡ phOf l s′
                → DnRfw l s → DnRfw l s′
dnRfw-relayAdvS l s s′ b ht peq peq′ hwf heq keq deq rw _ =
  dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl refl refl refl (sym peq′)
    (dnRfw-relayAdv b _ _ _ _ _ ht hwf
      (dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl heq (cong coarsenCSc keq) deq peq
        (rw (subst RelayRfw (sym peq) tt))))


------------------------------------------------------------------------
-- §6i(c)  (T11b) *** ITEM I's INTERFACE — THE NINTH CARRY, DESIGNED AND RE-COSTED.
-- Read this before pricing the carry again: the T11-review band 290-310 OMITS TWO
-- PIECES, and both were found by tracing the api arm's dispatch against the fields
-- above rather than by building anything. ***
--
-- *** THE DISPATCH, in the form it wants — and it needs NEITHER the fired LINK nor
-- the server's fixity, which is the one thing that came out CHEAPER than priced. ***
-- Dispatch the GUARD at the SUCCESSOR first (`dnRfw-relayAdvC` and `dnRfw-enter` are
-- both stated at `s′`), then the cone's `DnCsDrv` field, and every arm closes:
--
--   · `relayOf l s′ ≡ producing b pp2`, `DnCsDrv` on its LANDING arm → the second
--     landing (`DnCsAwLand`) gives `csWar` and `dnRfw-enter` builds the whole record.
--     *** It does not matter what node D did, nor which link fired: *** the keystone
--     REBUILDS rather than transports, and on an up-link arm the landing is refuted
--     by the link and the case is vacuous.
--   · `… pp2`, `DnCsDrv` on its FIXITY arm → the relay AND the server are fixed, so
--     the guard transports backwards: `dnRfw-frame` (node D fixed) or
--     `dnRfw-nodeDApi` (node D fired, with `pipeInv⇒inCp03` at the SOURCE).
--   · `relayOf l s′ ≡ producing b pp3`, LANDING arm, `RelayAdv` present → the
--     three-outcome `relayAdvRfw`: `rsOut` is refuted by the successor's own guard,
--     `rsEnter` by the phase clash `pp2 ≢ pp3`, and `rsAdv` IS the arm —
--     `dnRfw-relayAdvC` with the THIRD landing.  Compose `dnRfw-cliApi` before it if
--     node D moved in the same sync (the two classes are independent: one moves
--     `ca`/`x` at fixed `rx`, the other moves `sa`/`rx` at fixed `ca`/`x`).
--   · `… pp3`, FIXITY arm → frame / `dnRfw-nodeDApi`, as at `pp2`.
--   · the guard `⊥` at `relayOf l s′` → `dnRfw-out`, and nothing else is needed.
--
-- *** THE FIRST OMITTED PIECE — AN IMPOSSIBLE COMBINATION WITH NO REFUTATION, and
-- it is the cone's own §8 (i-b) trap. ***  The arm "`DnCsDrv` on its LANDING arm and
-- `RelayAdv` REPORTED AS FIXED" is unreachable — the cone sets the two fields from
-- the same peel, so a landing arm always comes with an advance — but the TYPES do not
-- say so, and at `pp3` the combination is NOT closable from the fields: the source is
-- then `pp3` too, its own field 1 admits `csIdle`, and field 7's antecedent at the
-- successor's `csWrf ht` has nothing to read.  *** THE FIX IS A CONE EDIT AND IT IS
-- NEARLY FREE: *** give `LiveLegApiCone.DnCsDrv`'s LANDING arm a fourth member
-- `RelayAdv x x′`.  All four producer arms already have `raR` in scope in the same
-- tuple (`LiveLegApiCone` §7/§8, the `, raR , lnkR` lines), so the edit is the type
-- plus four one-word additions plus `LiveDrvBF.drvCS-api-at`/`-at2`'s re-cut.
-- Estimated 15-25.  *** Do NOT try to refute the combination downstream: this is the
-- trap the cone banked at T8c-iii, and merging the correlation into ONE field is the
-- banked answer. ***
--
-- *** THE SECOND OMITTED PIECE, and it is the expensive one: `LiveDrvBFD`'s
-- `BFCliDrvAdj` HAS NO PRODUCER. ***  `LiveDrvBFD:498-506` declares it in
-- hypothesis position with no `bfCliDrvAdj-of` anywhere in the tree (grep: zero
-- hits), and the ninth factor's BlockFetch half cannot call `bfFresh-cliApi` without
-- one.  Its producer is §6c's twin one protocol over — six clauses, each inverting
-- node D's own step at the source phase through `bind-ev-inv` plus one
-- `Net_Api-≟` gate, then reading the BF client's row at that concrete label — and
-- §6c measures 110.  Estimated 90-120, at §6c's own price class.
--
-- *** <<< (T11c) THE SECOND PIECE IS RE-COSTED AGAIN, AND THE ESTIMATE BELOW IS
-- QUOTED SO A COPY CANNOT REINTRODUCE IT: *** "Estimated 90-120, at §6c's own price
-- class."  *** TRACED HOP BY HOP IT IS ≈175, and the reason is ONE hop. >>> ***
--
-- The good half first, because it is most of the object: FIVE of node D's six hops
-- need NO producer work at all.
--
--   · `cp0→cp1` and `cp1→cp2` fire `apiCS` labels, where `CliApiRowP` reduces to bare
--     FIXITY (`LiveLegApiCone:1086-1090`'s catch-all) — and `PhCli cp1`/`cp2` are `⊤`,
--     so the client's own region transports and the hop is a frame.
--   · `cp3→cp4` is FREE FROM A FACT ALREADY CARRIED: `LiveLegApiExpose`'s
--     `NodeDApiEvo.ndaBD` has a `cp3` ANCHOR (its sixth field) giving
--     `bfC-BD nd ≡ bcBlk1 b″` — the SOURCE client — and `CliFreshBF (bcAblk b) = ⊥`
--     refutes the hop outright.  This is `bfFresh-cliApi`'s `dbRecv` arm, and the
--     anchor was built for a different consumer at T10.
--   · `cp4→cp5` and `cp5→cp6` are refuted by the PHASE conjunct alone
--     (`PhCli cp4 = PhCli cp5 = ⊥`) and read no client fact at all.
--
-- *** THE ONE HOP THAT COSTS IS `cp2→cp3`, and it costs because of §0(6)'s own
-- hazard. ***  Its successor needs `PhCli cp3 = CliPostBF`, and `CliPostBF` excludes
-- `bcIdle` where `CliFreshBF` admits it — so on `CliApiRowP`'s FIXITY arm the state
-- `(cp3 , bcIdle)` is exactly the unreachable-but-unexcluded one, and only "node D's
-- BF client CO-FIRED" excludes it.  That is §2b⁵'s sharpening on the BlockFetch axis.
--
-- *** WHAT IS ALREADY THERE, AND WHAT IS NOT — checked, not guessed. ***
-- `PipeBundleRecv.bundleBF-ev-forces` (`:148-155`) is ALREADY GENERIC in the BF event
-- AND in the result type, so the bundle half of the sharpening is free — it is what
-- `bundle-recv-cliPos`/`bundle-recvBFBlock-forces-src` are both built from.  What is
-- missing is the TAG-SPECIFIC pair its two handlers take: the frozen Value layer has
-- `recvBFBlock-forces-src` / `recvBFBlock-src-val` / `recvBFBlock-server-absurd` for
-- `recvBFBlock` and **NOTHING for `sendBFRequestRange`** (tree-wide grep over
-- `LTL/Value/`: zero hits).  Those two are the fine-position dispatches, and they are
-- the shape that is not cheap.
--
-- *** SO: two tag lemmas (≈60) + the bundle wrapper (≈25) + the `sendBFRequestRange`
-- edge pin (≈18) + the six-clause driver dispatch (≈70) ≈ 175. ***  Item I's honest
-- total is then ≈465-560 rather than ≈400-450, and the finish's own band wants
-- re-quoting before the carry is opened.  *** The five free hops are the part worth
-- reading twice: do not price this as six. ***
--
-- *** <<< (T11d) THE CARRY's OWN SIZE IS NOW MEASURED, NOT ESTIMATED, AND EVERY
-- FIGURE BELOW IS QUOTED SO A COPY CANNOT REINTRODUCE IT: *** "≈400-450", "the two
-- factors 250-320".  *** AS TWO SEPARATE TRAILING FACTORS THE ARMS COST ≈700-800. >>>
--
-- The measurement is the SEVENTH factor's own arm set, on the SAME down ChainSync
-- hop, counted in `LiveChanJoin`: `dnJointU-fill` 67 · `-read` 62 · `-api` 176 ·
-- `-frame` 12 · `-drain` 22 · `-break-at` 63 = **402 lines for ONE factor**.  A
-- separate factor needs its own six, because the arms are per-OBJECT even though the
-- extraction machinery under them is shared (`LiveChanJoinCS.setRead⁺`,
-- `cssRow-off`/`cscRow-off`, `LiveChanCS.srvSendRow`/`cliSendRow`, `csSend-⊥`,
-- `csFill-noPeer-⊥` — all reused verbatim, which is why the SHAPE is cheap and the
-- COUNT is not).  Two factors ⇒ ≈700-800, and T10's measured 290 for the EIGHTH
-- factor is not the precedent it looked like: that factor's arms delegated to
-- `LiveDrvBFA`'s existing `upJoint-*` builders instead of growing a set of their own.
--
-- *** THE FIX, AND IT CHANGES NO END STATE: DO NOT ADD TRAILING FACTORS — FOLD EACH
-- OBJECT INTO THE FACTOR THAT ALREADY WALKS ITS HOP. ***
--
--   · `DnRfw` belongs in the SEVENTH factor `LDC.DnJoint` (`DnFresh × DrvCliD`): same
--     down CS hop, same adjacencies, same six arms, and every datum its classes want
--     is already bound at each arm (`peq`, `cellSrc`/`cellTgt`, `deq`, the two row
--     disjunctions).  Each arm gains ONE component, ≈25-40 lines, not 402.
--   · `BFFresh` belongs in the FIFTH factor `LDB.DrvBF`: same down BF hop, and its
--     arms (`drvBF-fill`/`-api`/`-drain`/`-break`) already take the down BF server's
--     io row and the relay's phase fixity.
--   · the token `InCp03` the api class wants is `LegJoint`'s first factor three
--     projections deep — `upSent-of` (`LiveChanJoin:1705-1712`) is the route, already
--     written.
--
-- *** Estimated for the FOLDED shape: ≈250-350 for both objects, against ≈700-800 for
-- two new factors.  The five `mkU` arguments the coordinator costed are real but they
-- are not where the money is: the ARMS are. ***
--
-- *** SO ITEM I RE-COSTS AT ≈400-450, not 290-310 *** (T10's measured eighth factor
-- 290 + the two pieces above), which takes the task to ≈970-1,030 against the
-- chartered STOP 1,000 — and the campaign's standing rule is to STOP on a growth
-- discovery rather than ride a paid checkpoint into it.  Everything above this note
-- is green, committed and consumed by a passing acceptance probe; the carry and the
-- discharge are the residual, with the dispatch settled arm by arm.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §6c  *** (T8c-ii) THE JOINT ADJACENCY'S PRODUCER — `CliDrvAdj`, TOTAL ON THE
-- DRIVER'S SIX HOPS. ***  The object §5 declared hypothesis-position now has one.
--
-- *** WHAT MAKES IT POSSIBLE, and it is not the same thing at every hop. ***  Each
-- clause inverts the driver's OWN STEP at the source phase, which pins the fired
-- LABEL exactly (`consume`'s six events are literals — `SysNode.decCons:933-958`), and
-- then reads the client's fact at that concrete label:
--
--   · the THREE ChainSync hops (`c01`, `c12`, `c56`) need the client to have MOVED,
--     and the fact that says so is `LiveLegApiCone` §2b⁵'s SHARPENING — the client's
--     genuine row at its own key.  §4b's three EDGE pins then name both endpoints of
--     the row, which is exactly what `cdReq`/`cdRecvF`/`cdDone` index on.  *** The
--     fixity-or-row DISJUNCTION is useless at these three hops: at `c01` it would give
--     `CliDrvAdj ccIdle cp0 ccIdle cp1`, which is EMPTY. ***
--   · the THREE BlockFetch hops (`c23`, `c34`, `c45`) need the client to have STAYED,
--     and there the disjunction is exactly right: at an `apiBF` label
--     `LiveCSRow.CScApiRowP` reduces to its catch-all, which IS the fixity, so the
--     label inversion alone closes them and no pin is read.  (`LiveLegApiCone`'s
--     `bfAt⇒cscFix` does this same reduction behind a `BfAt` pin; here the label is
--     already a literal, so the pin would be a detour.)
--
-- *** WHY THE STEP AND NOT `IoOffers`. ***  §6/§6b's refusal family is keyed by a
-- CONCRETE label, so using it would need the label first — and the only thing that
-- gives the label is the step.  With the step in hand the refusals are not needed at
-- all here: they remain what they were built for, the COMPLETENESS argument for
-- `CliDrvAdj`'s four omitted rows.
--
-- *** THE `>> Skip` BIND IS CROSSED BY `bind-ev-inv`, and the head's own offer map by
-- ONE `Net_Api-≟` `with` *** — `WalkDAnchor.consD-c34-anchor`'s idiom verbatim, six
-- times.  Two of the six heads are OUTPUTS (`cp2`, `cp4`) whose offer map has a SECOND
-- gate on the value; it is never reached, because once `Net_Api-≟` answers `yes refl`
-- the event is pinned and the client's fact reduces on the label alone.
------------------------------------------------------------------------

-- §2b⁵'s sharpening at COARSE positions — `CscCliFired`'s own body with `coarsenCSc`
-- already applied.  This file's objects (`CliDrvAdj`, `CliAt`, `DnFreshC`) are all
-- coarse, so stating the producers here saves a `coarsen` on every clause
CsCliRow : (l : Link) (cl : Dir) (ca ca′ : NS.CScPos) {X : Set 0ℓ}
           (e : Net_Api Payload X) (a : X) → Set
CsCliRow l cl ca ca′ {X} e a = CsAt l cl e a → NS.csCnxt l cl ca (X , e) a ≡ just ca′

-- … and the bridge, which is the IDENTITY: `LiveCSRow.CScRow` is stated through
-- `coarsenCSc` already, so the coarse form and the cone's fine form are the same type.
-- Machine-checked here rather than asserted — the campaign has paid once for a pair of
-- accessors that looked convertible and were not (`LiveRelayCS.dnCSs-is-of`)
cscCliFired⇒row : (l : Link) (cl : Dir) (csc csc′ : SN.CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → CscCliFired l cl csc csc′ e a
  → CsCliRow l cl (coarsenCSc csc) (coarsenCSc csc′) e a
cscCliFired⇒row l cl csc csc′ h = h

-- (1) the `cp0 → cp1` hop — *** THE ONE THE WHOLE SHARPENING EXISTS FOR. ***  The
-- driver's head at `cp0` is `consume l hi`, whose first event is
-- `apiCS l hi sendCSRequestNext`; §2b⁵ says node D's own client fired it, and §4b's
-- edge pin says that row is `ccIdle → ccWreq`
cliDrvAdj-c01 : (l : Link) (b : Block₃) (ca ca′ : NS.CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b cp0) ─[ ev (evl (evLabel X e a)) ]─► M
  → CsCliRow l hi ca ca′ e a
  → CliDrvAdj ca cp0 ca′ cp1
cliDrvAdj-c01 l b ca ca′ {X} {e} {a} step fired
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp0) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiCSCar sendCSRequestNext , apiCS l hi sendCSRequestNext) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → CliDrvAdj z cp0 ca′ cp1) (sym (proj₁ edge))
          (subst (λ z → CliDrvAdj NS.ccIdle cp0 z cp1) (sym (proj₂ edge)) cdReq)
        where edge = cscReqEdge l hi ca a ca′ (fired refl)

-- (2) the `cp1 → cp2` hop: the head is the INPUT prefix
-- `apiCS l hi recvCSRollforward ⟶ consume-k l hi`, and the edge pin names the source
-- `ccArf ht` the row leaves — the half `cscRfwLands` alone does not give
cliDrvAdj-c12 : (l : Link) (b : Block₃) (ca ca′ : NS.CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b cp1) ─[ ev (evl (evLabel X e a)) ]─► M
  → CsCliRow l hi ca ca′ e a
  → CliDrvAdj ca cp1 ca′ cp2
cliDrvAdj-c12 l b ca ca′ {X} {e} {a} step fired
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp1) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiCSCar recvCSRollforward , apiCS l hi recvCSRollforward) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → CliDrvAdj z cp1 ca′ cp2) (sym (proj₁ (proj₂ edge)))
          (subst (λ z → CliDrvAdj (NS.ccArf (proj₁ edge)) cp1 z cp2)
                 (sym (proj₂ (proj₂ edge))) (cdRecvF (proj₁ edge)))
        where edge = cscRfwEdge l hi ca a ca′ (fired refl)

-- (3) the `cp2 → cp3` hop: the head is the OUTPUT
-- `apiBF l hi sendBFRequestRange ! … ⟶ …`, so the fired label is a BlockFetch one and
-- the client's api fact reduces to its FIXITY on the label alone
cliDrvAdj-c23 : (l : Link) (b : Block₃) (csc csc′ : SN.CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b cp2) ─[ ev (evl (evLabel X e a)) ]─► M
  → CScApiRowP l hi csc csc′ e a
  → CliDrvAdj (coarsenCSc csc) cp2 (coarsenCSc csc′) cp3
cliDrvAdj-c23 l b csc csc′ {X} {e} {a} step rowP
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp2) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiBFCar sendBFRequestRange , apiBF l hi sendBFRequestRange) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → CliDrvAdj (coarsenCSc csc) cp2 (coarsenCSc z) cp3) rowP
              (cdBF23 (coarsenCSc csc))

-- (4) the `cp3 → cp4` hop: the INPUT prefix `apiBF l hi recvBFBlock ⟶ …`
cliDrvAdj-c34 : (l : Link) (b : Block₃) (csc csc′ : SN.CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b cp3) ─[ ev (evl (evLabel X e a)) ]─► M
  → CScApiRowP l hi csc csc′ e a
  → CliDrvAdj (coarsenCSc csc) cp3 (coarsenCSc csc′) cp4
cliDrvAdj-c34 l b csc csc′ {X} {e} {a} step rowP
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp3) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiBFCar recvBFBlock , apiBF l hi recvBFBlock) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → CliDrvAdj (coarsenCSc csc) cp3 (coarsenCSc z) cp4) rowP
              (cdBF34 (coarsenCSc csc))

-- (5) the `cp4 → cp5` hop: the OUTPUT `apiBF l hi sendBFClientDone ! tt ⟶ …`
cliDrvAdj-c45 : (l : Link) (b : Block₃) (csc csc′ : SN.CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b cp4) ─[ ev (evl (evLabel X e a)) ]─► M
  → CScApiRowP l hi csc csc′ e a
  → CliDrvAdj (coarsenCSc csc) cp4 (coarsenCSc csc′) cp5
cliDrvAdj-c45 l b csc csc′ {X} {e} {a} step rowP
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp4) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiBFCar sendBFClientDone , apiBF l hi sendBFClientDone) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → CliDrvAdj (coarsenCSc csc) cp4 (coarsenCSc z) cp5) rowP
              (cdBF45 (coarsenCSc csc))

-- (6) the `cp5 → cp6` hop: the head is `apiCS l hi sendCSDone ⟶₀ Ret b`, the third
-- and last ChainSync hop, and §4b's third edge pin names it `ccIdle → ccWdone`
cliDrvAdj-c56 : (l : Link) (b : Block₃) (ca ca′ : NS.CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b cp5) ─[ ev (evl (evLabel X e a)) ]─► M
  → CsCliRow l hi ca ca′ e a
  → CliDrvAdj ca cp5 ca′ cp6
cliDrvAdj-c56 l b ca ca′ {X} {e} {a} step fired
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp5) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiCSCar sendCSDone , apiCS l hi sendCSDone) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → CliDrvAdj z cp5 ca′ cp6) (sym (proj₁ edge))
          (subst (λ z → CliDrvAdj NS.ccIdle cp5 z cp6) (sym (proj₂ edge)) cdDone)
        where edge = cscDoneEdge l hi ca a ca′ (fired refl)

-- *** `ConsAdv` IS IRREFLEXIVE, and the carry needs it. ***  Every one of the six
-- hops changes the phase, so a step reported as FIXED at node D's driver slot cannot
-- also be reported as an advance.  This is what makes `deNodeDBD`'s two arms mutually
-- exclusive AT THE CONSUMER rather than merely by construction — the property the
-- T8c-ii shape lacked (see §8 (i-b))
consAdv-irr : (x : ConsPh) → ConsAdv x x → ⊥
consAdv-irr cp0 ()
consAdv-irr cp1 ()
consAdv-irr cp2 ()
consAdv-irr cp3 ()
consAdv-irr cp4 ()
consAdv-irr cp5 ()
consAdv-irr cp6 ()

-- *** THE TOTAL DISPATCH — one clause per `ConsAdv` row, and the phase pair is what
-- selects the hop. ***  `cp6` is not a source of any row (`Ret b >> Skip` has no
-- visible step), so six clauses are the whole of it, and a new `ConsAdv` row is a
-- coverage error HERE rather than a silently-unproducible adjacency
cliDrvAdj-of : (l : Link) (b : Block₃) (x x′ : ConsPh) (csc csc′ : SN.CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b x) ─[ ev (evl (evLabel X e a)) ]─► M
  → ConsAdv x x′
  → CScApiRowP l hi csc csc′ e a
  → CscCliFired l hi csc csc′ e a
  → CliDrvAdj (coarsenCSc csc) x (coarsenCSc csc′) x′
cliDrvAdj-of l b _ _ csc csc′ step c01 rowP fired =
  cliDrvAdj-c01 l b _ _ step (cscCliFired⇒row l hi csc csc′ fired)
cliDrvAdj-of l b _ _ csc csc′ step c12 rowP fired =
  cliDrvAdj-c12 l b _ _ step (cscCliFired⇒row l hi csc csc′ fired)
cliDrvAdj-of l b _ _ csc csc′ step c23 rowP fired = cliDrvAdj-c23 l b csc csc′ step rowP
cliDrvAdj-of l b _ _ csc csc′ step c34 rowP fired = cliDrvAdj-c34 l b csc csc′ step rowP
cliDrvAdj-of l b _ _ csc csc′ step c45 rowP fired = cliDrvAdj-c45 l b csc csc′ step rowP
cliDrvAdj-of l b _ _ csc csc′ step c56 rowP fired =
  cliDrvAdj-c56 l b _ _ step (cscCliFired⇒row l hi csc csc′ fired)

------------------------------------------------------------------------
-- §7  FALSIFICATIONS — ONE PER NOVEL FAMILY IN THIS FILE.  TWENTY-TWO: T8a's SIX
-- (F50-F55), T8b's FIVE (F56-F60), the fix round's TWO (F61, F63), T8c-0's ONE
-- (F64), the T8c-ii prose round's ONE (F65, §7c) and T8c-ii's FOUR (F66-F69, §7d)
-- and T8c-iii's THREE (F74-F76, §7e) — plus the RE-RUNS of F55, F56 and F61.  *** THE NUMBERING HAS ONE HOLE: F62
-- WAS NEVER RUN *** — the fix round's guards went F61 then F63, so the number was
-- SKIPPED, not dropped and not lost.  All arity-preserving, all RUN, all RED, all reverted byte-identically
-- (`git diff --stat` verified EMPTY after each).  T8a's six families: the four-node
-- lift's node identity, the peer offer's landing, the coupling's region, the driver
-- offer's continuation, §4's server region, and §4's correlation field.  T8b's five:
-- §4's PHASE GUARD, §5's joint node-D adjacency, §4's NARROWED cell arm, §5c's
-- io-CLOSURE of the coupling's region, and §6's label refusal.
--
-- *** EACH RECORD'S LINE NUMBERS ARE AS-RUN AT THE REVISION NAMED IN ITS ENTRY, ***
-- not as-of the current file: F50-F53 were run at `6c66b33`, F54/F55 at `17af1d5`,
-- F56-F60 and F55's RE-RUN at *** `843e079` *** (the whole round was run after §6
-- landed — "T8b's own commits" was not a revision, the review's M-2), and the fix
-- round's F56-re-run/F61/F63 at *** `9e450ee` ***.  The file has grown four times
-- since, so do not "correct" the older citations against today's line numbers.
--
-- *** READ `LiveRelayCS` §7's RE-AIMING RULE BEFORE DISCHARGING ANYTHING THAT
-- MAKES ONE OF THESE VACUOUS. ***  A guard whose target clause has become `⊤` (or
-- whose target lemma has lost its consumer) guards NOTHING.
--
-- *** (T8b) THE RE-AIMING AUDIT OF T8a's SIX, done rather than assumed. ***  T8b
-- narrowed §4's cell arm, phase-GUARDED the clause and split the record into
-- `DnFreshC` plus the guarded `DnFresh`.  Disposition, family by family: F50/F51/F53
-- untouched (their targets are §2/§3's kit, which T8b did not edit); F52 LIVE —
-- `CliPost` is unchanged and `cliPost-idle-⊥` still has its one consumer
-- `freshIdle⇒cp0`, and F59 now guards the same region at the OTHER end (its io
-- closure); F54 LIVE — `SrvFresh` and `srvFresh⇒areq` are unchanged; F55 *** RE-RUN,
-- because its target field's TYPE changed *** (it moved into `DnFreshC` and its
-- conclusion narrowed to `ReqOnly`) — see the re-run recorded with its entry.  No
-- guard of T8a's became vacuous, and none was disposed of by assertion.
--
-- *** WHAT T8c MUST RE-AIM. ***  If T8c moves §4's clause into `LiveDrvBF.DrvCp` as
-- POSITION clauses, F54/F55/F56 must be re-aimed at the moved clause (their targets
-- are the REGION, the CORRELATION and the GUARD, not this file's record); if it
-- widens `CliDrvAdj` with a seventh row, F57 must be re-aimed at the new row's own
-- landing; and if it ever restores the WIDE `ReqFull` cell arm, F58 stops guarding
-- anything because the narrowing it guards would be gone (that is the honesty case
-- the T7 rule names — a guard with no funded clause left to guard).
--
-- (F50  THE FOUR-NODE LIFT, `nodes-offer-D`)  swap the two inner sibling
--      refusals — `absNodeC-no-when-D (nC s)` and `absNodeB-no-when-D (nB s)` —
--      keeping the `⦀-ev-R` ladder and both fingerprints.  *** RED ***
--      `LiveDrvCSD.agda:276.25-73: error: [UnequalTerms] Fin.zero !=
--      Fin.suc (fromℕ< _)`, i.e. `viewV (force (absNodeB (nB s))) … ≡ nothing`
--      offered where `absNodeC (nC s)`'s was expected.  What it establishes: the
--      three refusals are NOT interchangeable even though their TYPES are the same
--      12-way fingerprint — the operand order of the four-node `⦀` is load-bearing
--      and this ladder really is node D's row of it, not a copy of another node's.
--
-- (F51  THE PEER OFFER, `peer-cD0`)  land the client at `SN.csDone1` instead of
--      `SN.csReqNext1` (both are concrete `CScPos` constructors, both are
--      `ccIdle` successors, so the mutation is type-correct in the argument
--      position and only the ROW disagrees).  *** RED ***
--      `:378.3-382.36: [UnequalTerms] NS.ccWdone != NS.ccWreq of type
--      NS.CScPos`.  What it establishes: the offer is pinned to `ceqCSc01`'s own
--      row — the FIRST of `ccIdle`'s three api rows (`NodeSpecs:306-308`) — and
--      cannot be satisfied by the `sendCSDone` row (`:312-314`) that
--      `LiveRelayOpen.peer-cp5` uses.  This is the guard against the one collapse
--      that would be invisible in prose: `peer-cD0` is `peer-cp5`'s body with one
--      row changed, and a revert-by-string would silently reinstate the twin.
--
-- (F52  THE COUPLING's REGION, `CliPost`)  put `ccIdle` INSIDE the `cp1` region
--      (`CliPost NS.ccIdle = ⊤`).  *** RED ***  `:173.1-18: [ShouldBeEmpty]
--      CliPost NS.ccIdle should be empty … when checking the clause left hand side
--      cliPost-idle-⊥ ()`.  What it establishes: `cliPost-idle-⊥` is the ONE place
--      the region's exclusion of `ccIdle` is used, and it is a real consequence of
--      the region rather than of the dispatch's shape — so the client-antecedent
--      reading of §1 ("a client at `ccIdle` leaves `cp0` as the only phase") is
--      earned by `CliPost` and not by the `⊤` clauses around it.
--
-- (F53  THE DRIVER OFFER's CONTINUATION, `consVis-cp0`)  retarget the visible map
--      at `decCons l hi b₀ cp2` instead of `cp1`.  *** RED ***
--      `:360.41-45: [UnequalTerms]` with both trees printed in full — the `cp2`
--      decode is the `sendBFRequestRange` chain, the `cp1` decode the
--      `recvCSRollforward` prefix.  What it establishes: the offer identifies
--      `consume`'s SECOND event as the continuation, so `cp0`'s decode really is
--      the FIRST LINK OF THE STRAIGHT CHAIN (`FourNodeDiamond:238-240`) and the
--      driver's step is that chain's first hop — the concrete refutation of §8.2's
--      "a LOOP head, not a literal prefix" pricing concern.  (§3's corrected note:
--      there is no loop anywhere in `consume`/`consume-k`, so the premium was never
--      real — the T8 review's M-1.)
--
-- (F54  §4's SERVER REGION, `SrvFresh`)  admit `csCanAwait` into the fresh region
--      (`SrvFresh NS.csCanAwait = ⊤`).  *** RED ***  `:582.1-35: [ShouldBeEmpty]
--      SrvFresh NS.csCanAwait should be empty … when checking the clause left hand
--      side srvFresh⇒areq NS.csCanAwait () _`.  What it establishes: the
--      sharpening's eleven absurd clauses are carried by the REGION and not by the
--      dispatch, so `srvFresh⇒areq` really is the statement "inside this region,
--      refuting `csIdle` leaves `csAreq`" and not a tautology on `CSsPos`.  It is
--      also the guard the gate's §0.3 finding needs: `csCanAwait` is one of the
--      eleven positions with no enabled hidden move at `cp6` AMONG THE FOUR
--      COMPONENTS ENUMERATED (§4's scoping note (b)), so if it ever re-enters the
--      region the arm becomes unprovable FROM THESE FACTS rather than merely dearer.
--
-- (F55  §4's CORRELATION, `DnFresh.dfArr`)  weaken the correlation's antecedent
--      from `≡ NS.csIdle` to `≡ NS.csAreq` (still a well-typed field, still about
--      the same two slots).  *** RED ***  `:662.49-53: [UnequalTerms] NS.csIdle !=
--      NS.csAreq of type NS.CSsPos when checking that the expression hidl has
--      type …`.  What it establishes: the `(empty , ccAwait)` sub-case is closed by
--      the correlation AT `csIdle` and by nothing else — the four bare conjuncts
--      do not reach it, which is precisely why the clause has a fifth field.  A
--      successor tempted to drop `dfArr` as redundant should run F55 first.
--
--      *** (T8b) RE-RUN, because the field moved into `DnFreshC` and its conclusion
--      narrowed from `ReqFull` to `ReqOnly`. ***  The SAME mutation, at the new
--      types: *** RED ***  `:879.49-53: error: [UnequalTerms] NS.csIdle != NS.csAreq
--      of type NS.CSsPos when checking that the expression hidl has type
--      SStep.coarsenCSs (dnCSsOf l (RState.sys r)) ≡ NS.csAreq`.  So the guard is
--      live at the narrowed type too, and the disposition above is measured rather
--      than asserted.
--
-- ============ T8b's FIVE ============
--
-- (F56  §4's PHASE GUARD, `RelayFresh`)  admit the successor of the relay's own
--      request emit into the guard region (`RelayFresh (producing b pp1) = ⊤`), a
--      single clause-value flip on a total dispatch.  *** RED ***
--      `LiveDrvCSD.agda:993.1-33: error: [ShouldBeEmpty] RelayFresh (producing b
--      pp1) should be empty, but that's not obvious to me — when checking the clause
--      left hand side relayCs-guard-⊥ _ _ (rcReq _) ()`.  What it establishes: *** the
--      guard's exclusion of `pp1` is the ENTIRE mechanism by which the review's I-2
--      step (`csAreq + reqCSRequestNext → csCanAwait`) is refuted. ***  Nothing else
--      in the object reaches that step — not the cell conjunct, not the client
--      conjunct, not node D's phase conjunct — so a successor who drops the guard, or
--      who widens it "harmlessly" by one producing sub-phase, turns `DnFresh` from an
--      invariant into a false statement.  This is the guard on the finding that
--      `DnFresh` is NOT an unconditional state invariant.
--
-- (F57  §5's JOINT NODE-D ADJACENCY, `CliDrvAdj`)  retarget the request row's
--      LANDING phase, `cdReq : CliDrvAdj ccIdle cp0 ccWreq cp1` becoming `… ccWreq
--      cp2` (both are `ConsPh` constructors, both are reachable phases, so the
--      mutation is type-correct and only the driver's own chain disagrees).  *** RED
--      ***  `:1022.40-42: error: [UnequalTerms] (Level.Lift _ℓ_863 U.⊤) !=< ⊥ when
--      checking that the expression tt has type PhFresh cp2`.  What it establishes:
--      the surviving arm of node D's api class is pinned to the driver's ACTUAL
--      advance `c01` and not merely to "some advance" — the class is sound because
--      `sendCSRequestNext` moves `cp0 → cp1`, and if the joint adjacency were allowed
--      to skip a link of the chain the successor would fall outside `PhFresh` and the
--      class would be unprovable.  It is also the guard on the phase conjunct's
--      exactness: `PhFresh` is `{cp0, cp1}` and not `{cp0 … cp2}`.
--
-- (F58  §4's NARROWED CELL ARM, `ReqOnly`)  re-pin the arm's message from
--      `MsgCSRequestNext` to `MsgCSAwaitReply` (a different `MessageChainSync`
--      constructor; the predicate keeps its arity, its leniency in `(time , mode ,
--      length)` and its polarity).  *** RED ***  `:953.51-55: error: [UnequalTerms]
--      MsgCSAwaitReply != MsgCSRequestNext of type MessageChainSync when checking
--      that the expression refl has type MsgCSAwaitReply ≡ MsgCSRequestNext`, i.e. at
--      *** `reqOnly-not`'s `no refl` (`:953`) and not at `reqOnly-rn` (`:957`, one
--      definition later, which would have failed second) — the review's M-1 ***.
--      What it establishes: the narrowed arm is pinned to *** the very
--      message node D's own wire-send writes *** (`csCnxt:315-320`, `rnPayload`), so
--      the review's I-1 narrowing is not merely safe but forced from both ends — the
--      client's fill ESTABLISHES exactly this message and the server's read CONSUMES
--      exactly it.  Re-widening the arm (back to `LiveChanCS.ReqFull`) does not break
--      this guard; it breaks `dnFresh-srvRead`'s `srFI` clause, which is the defect
--      I-1 found.
--
-- (F59  §5c's io CLOSURE OF THE COUPLING's REGION, `CliPost`)  admit `ccInt` into the
--      `cp1` region (`CliPost NS.ccInt = ⊤`) — the F52 mutation at a DIFFERENT
--      position, and deliberately so: F52 guards the region's exclusion of `ccIdle`
--      (which the coupling's client-antecedent reading needs) and F59 guards its
--      io CLOSURE (which the coupling's PRESERVATION needs).  *** RED ***
--      `:1286.1-41: error: [ShouldBeEmpty] CliAt cp1 …LiveChanCS.NS.ccInt should be
--      empty, but that's not obvious to me — when checking the clause left hand side
--      drvCliD-read-at _ _ _ cp1 (crIF _ _) ()`.  What it establishes: the region is
--      io-closed BECAUSE `ccInt` is outside it — an intersect-awaiting client's two
--      reads land at `ccAif`/`ccAin`, which are NOT in `CliPost`, so admitting
--      `ccInt` would break the read class rather than merely enlarge the region.
--      The `cp1` clause of §1's coupling cannot be widened at will.
--
-- (F60  §6's LABEL REFUSAL, `consDVis-no-fi`)  retarget the whole family at
--      `sendCSRequestNext` instead of `sendCSFindIntersect` (signature and
--      conclusion; `consD-no-fi`'s type follows, so the mutation stays well-formed
--      and arity-preserving).  *** RED ***  `:1378.50-54: error: [UnequalTerms] just
--      ((go p >>= Prefix (go p) (apiCS l hi recvCSRollforward) (consume-k l hi)) (λ _
--      → Ret (go p) (lift tt))) != nothing of type Maybe (PTree …)` — the `cp0` clause,
--      with the driver's ACTUAL continuation printed in full: `consume`'s tail after
--      `sendCSRequestNext`, bound under the `>> Skip`.  What it establishes: the
--      family COMPUTES the driver's visible map rather than being vacuous on it — at a
--      phase where the label IS offered the same clause shape fails, and it fails by
--      exhibiting the offer.  It also machine-checks the `>> Skip` crossing: the
--      printed term is the inner continuation ALREADY bound, so `nothing` really does
--      propagate through the bind by computation and no inversion was needed.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7b  (T8b FIX ROUND) TWO NEW FALSIFICATIONS AND ONE RE-RUN.
--
-- *** (F56  RE-RUN, because its target MOVED.) ***  The three-row `RelayCsAdj` and its
--      `relayCs-guard-⊥` were replaced by `RelayAdv` and the TOTAL dispatch
--      `relayAdv-guard` (§5d), so F56's red site moved with them -- the F48/F49
--      re-aiming rule APPLIED rather than asserted.  Same mutation (`RelayFresh
--      (producing b pp1) = ⊤`), at the new site: *** RED ***  `:1084.48-49: error:
--      [ShouldBeEmpty] RelayFresh (producing b pp1) should be empty, but that's not
--      obvious to me -- when checking that the expression λ () has type RelayFresh
--      (producing b pp1) → ⊥`.  It now guards TEN clauses instead of three (the
--      `raCp6` row and all nine `raProd` rows), which is the coverage the fix round
--      bought.  (Run at `9e450ee`.)
--
-- (F61  *** THE C-1 DEFECT ITSELF -- the falsification that matters most in this
--      file. ***)  Restate the `raCp6` row as `RelayAdv (consuming b cp6) (consuming b
--      cp6)`, i.e. put the relay's `cp6` step back INSIDE the consuming half -- which
--      is exactly what the first shipment's completeness argument ("the relay's
--      consuming half fires on the UP link") asserted.  *** RED ***  `:1067.49-56:
--      error: [UnequalTerms] consuming b cp6 != producing b pp1 of type CPPh when
--      checking that the expression raCp6 b has type RelayAdv (consuming b cp6)
--      (producing b pp1)`.  What it establishes: *** `relayAdv-of`'s own `cp6` clause
--      DEMANDS the down-link landing, and prints the required pair. ***  So C-1 was
--      not a matter of taste: the classifier's answer at `cp6` is `producing b pp1`
--      (`WalkClassify.cpAdv-of:252-254`, `PipeEvRelay.cpStepKind-of:135-140`), the row
--      must say so, and with the row absent or mis-aimed there is NO clause to give --
--      the class was vacuous at the first arm's own sub-phase, and the extractor is
--      what makes that impossible to reintroduce silently.  (Run at `9e450ee`.)
--
-- (F63  §6b's POSITIVE COMPLEMENT, `consDVis-req-off`)  move the excluded phase from
--      `cp0` to `cp1` (the premise and the two clause bodies swap; arity, shape and
--      leniency preserved).  *** RED ***  `:1593.52-56: [UnequalTerms] just ((go p >>=
--      Prefix (go p) (apiCS l hi recvCSRollforward) (consume-k l hi)) (λ _ → Ret (go
--      p) (lift tt))) != nothing`, at the `cp0` clause, with the driver's actual
--      continuation printed.  What it establishes: the positive complement really
--      PINS the offering phase -- at `cp0` the driver DOES offer `sendCSRequestNext`,
--      so "offered nowhere else" is false the moment its own phase is let back in.
--      F60's twin at the other polarity: F60 shows the NEGATIVE family computes, F63
--      shows the POSITIVE one is not vacuously wide.  (Run at `9e450ee`.)
--
-- (THE THREE ABSENT-LABEL MEMBERS of §6b -- `recvCSRollback`, `recvCSIntersectFound`,
--      `recvCSIntersectNotFound` -- are F60's FAMILY and not a new one: same statement,
--      same shape, same computation, a different tag.  A fourth guard of that shape
--      would guard nothing F60 does not already guard, so per the campaign's
--      one-per-FAMILY rule none was run -- and this parenthesis is the declaration of
--      that decision rather than a silent omission.)
--
-- *** AND THE FIX ROUND's OWN RE-AIMING AUDIT, done not assumed. ***  The round
-- replaced `RelayCsAdj` (hence F56, re-run above) and touched nothing else a guard
-- points at: F52/F54/F55/F57/F58/F59/F60 all keep their targets byte-identical
-- (`CliPost`, `SrvFresh`, `DnFreshC.dfArr`, `CliDrvAdj.cdReq`, `ReqOnly`, `CliPost`
-- again at the io end, `consDVis-no-fi`), and F50/F51/F53 are §2/§3's kit, unedited.
-- `CliDrvAdj` gained NO row, so F57 still guards its only funded landing.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7c  (T8c-0) THE THREADING's OWN GUARDS.
--
-- *** (F61  RE-RUN AT ITS MOVED TARGET.) ***  `RelayAdv` and the `cp6` row moved to
--      `LiveLegApiCone`, so F61 moved with them — the F48/F49 rule, applied a second
--      time in two rounds.  SAME mutation (restate `raCp6` as `RelayAdv (consuming b
--      cp6) (consuming b cp6)`), at the cone: *** RED ***  `LiveLegApiCone.agda:
--      2594.24-31: error: [UnequalTerms] consuming b cp6 != producing b pp1 of type
--      CPPh when checking that the expression raCp6 b has type RelayAdv (consuming b
--      cp6) (producing b pp1)` — now at `cpStepKindQ-of⁺`'s OWN `cp6` clause, which is
--      a STRONGER site than the standalone extractor it replaced: the classifier every
--      relay arm already calls is what demands the down-link landing.
--
-- (F64  *** THE THREADING ITSELF — a wrong-ARM field. ***)  In `driverExpose⁺`'s
--      node-B arm, swap the two new relay fields: report node B's advance as leg CD's
--      (`deRelayAdvCD = inj₂ raB`) and leg BD's as fixity (`deRelayAdvBD = inj₁ refl`).
--      Arity-preserving, both fields still inhabited-looking, and it is exactly the
--      mis-wiring a six-arm hand-threading invites.  *** RED ***
--      `LiveLegApiExpose.agda:1062.33-37: error: [UnequalTerms] (SN.cp-B (nB s)) !=
--      (SN.cp-B nb′) of type CPPh when checking that the expression refl has type
--      SN.cp-B (nB s) ≡ SN.cp-B nb′`.  What it establishes: *** the FIXITY half of each
--      field is load-bearing — a leg whose relay DID fire cannot be reported as fixed,
--      so the six arms cannot be cross-wired silently. ***  Note WHICH half caught it:
--      not the advance (whose type would also have clashed) but the `inj₁ refl` left
--      behind — which is why the fixity-or-fired shape is the right thing to thread
--      rather than a bare advance under an existential.
--
-- (The node-D threading's own guard: *** the ground first given was too strong (M-3).
--      *** The LEG SWAP — `deConsStepCD = inj₂ drvD` inside the `ndaBD` arm — IS
--      arity-preserving and does go red, so a guard was available at zero design cost;
--      the honest statement is "the mutation is a TYPE ERROR by construction (both
--      decodes are literal in the field's type) and F64 already guards this wiring
--      class", not "there is no such mutation".
--
--      (F65  THE NODE-D THREADING's LEG)  in the `ndaBD` arm, report node D's BD step
--      as leg CD's (`deConsStepCD = inj₂ drvD`, `deConsStepBD = inj₁ (sym cCDeq)`).
--      *** RED ***  `LiveLegApiExpose.agda:1217.38-43: error:
--      [MismatchedProjectionsError] The projections …NodeStateD.cons-CD and
--      …NodeStateD.cons-BD do not match when checking that the expression cCDeq has
--      type SN.cons-BD nd′ ≡ SN.cons-BD (nD s)`.  What it establishes: the two node-D
--      fields are pinned to their own LEG's slot by the field type, and — like F64 —
--      *** the half that catches the swap is the FIXITY one ***, whose co-leg equation
--      names the other slot's projection.  A distinct error CLASS from F64's
--      (`MismatchedProjectionsError` against `UnequalTerms`), which is why running it
--      was worth the one build the too-strong ground had declined.)
--
-- *** WHERE F64/F65 LIVE (M-5b). ***  Both mutate `LiveLegApiExpose`'s
--      `driverExpose⁺` arms, and both are recorded HERE because this file is where the
--      threaded facts are consumed.  A reader arriving at `DriverExposed⁺`'s
--      `deRelayAdvBD`/`deConsStepBD` fields is pointed here by the note at those
--      fields.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7d  (T8c-ii) THE SHARPENING's OWN GUARDS — FOUR, one per novel family of the
-- slice: the sharpening's REFUTING arm, its THREADING, §4b's new EDGE pin and §6c's
-- LABEL INVERSION.  All arity-preserving, all RUN, all RED, all reverted by STRING
-- INVERSION (never `git checkout --`, the T8c-0 slip) with `git status` verified clean
-- after each.  Line numbers are as-run at `69072e5`.
--
-- (F66  *** THE SHARPENING's REFUTING ARM — the direction clash itself. ***)  In
--      `LiveLegApiCone.cscCliFired-srv`, read the FIRST component of `cssRow-key`'s
--      pair instead of the second — i.e. refute with the LINK equation where the
--      DIRECTION equation is wanted.  Arity-preserving, both projections in scope, and
--      the mutation an author syncing §2b⁵ against §2b″ would actually make (there the
--      working projection IS `proj₁`, `cssReqLand-cli`'s own line).  *** RED ***
--      `LiveLegApiCone.agda:1498.19-1499.51: error: [UnequalTerms] Data.Fin.Base.Fin
--      (Params.numLinks …p) != Dir of type Set when checking that the expression proj₁
--      (cssRow-key l sv (coarsenCSs css) (CS.apiCSev l cl m) row) has type cl ≡ sv`.
--      What it establishes: the block's whole content is the DIRECTION clash — the key
--      pin's link half is not merely weaker, it is the wrong type, so the sharpening
--      cannot be closed by anything but `cl ≢ sv`.
--
-- (F67  *** §6c's LABEL INVERSION — the TAG. ***)  In `cliDrvAdj-c01`, `with` on
--      `Net_Api-≟` at `sendCSDone` instead of `sendCSRequestNext`.  Arity-preserving
--      and genuinely tempting: both tags are `⊤`-carried, both are in scope, and both
--      are ChainSync hops of the SAME driver — `cliDrvAdj-c56` is the clause that
--      really does use `sendCSDone`.  *** RED ***  `LiveDrvCSD.agda:1859.46-48: error:
--      [UnequalTerms] (CSP.Operators.Prefix-cont (…go p) (apiCS l hi
--      sendCSRequestNext) (λ _ → …Prefix … (apiCS l hi recvCSRollforward) (consume-k l
--      hi)) (X , e) a | …go p (U.⊤ , apiCS l hi sendCSRequestNext) (X , e)) != nothing
--      … when checking that the expression br has type nothing ≡ just _x`.  What it
--      establishes: the inversion is not a formality — a `with` on the wrong tag's
--      decision leaves the HEAD's own offer map stuck, so each of the six clauses is
--      pinned to its own phase's literal event and the six cannot be permuted.
--
-- (F68  *** THE THREADING — F64/F65's mutation at the NEW pair. ***)  In
--      `nodeD-api-BD-evo⁺`, report the fired sharpening as leg CD's and leg BD's as the
--      fixity half (`(inj₁ refl) (inj₂ cscFired)`).  *** RED ***
--      `LiveLegApiExpose.agda:397.19-23: error: [UnequalTerms] (SN.csC-BD nd) != csc′
--      of type CScPos when checking that the expression refl has type SN.csC-BD nd ≡
--      csc′`.  *** THIRD CONFIRMATION of F64's finding, and it is the same half again:
--      what catches the swap is the FIXITY `refl` on the other leg, not the fired
--      fact's type. ***  So the fixity-or-fired shape earns its keep a third time, and
--      the note at `deCsCliBD` says both halves are load-bearing on that ground.
--
-- (F69  *** §4b's NEW EDGE PIN — the source position. ***)  In
--      `LiveCSRow.cscReqEdge`, move the working clause from `ccIdle` to `ccWreq` and
--      give `ccIdle` the absurd body.  Arity-preserving, and the mutation an author
--      would make from the table's shape alone (`ccWreq` is where the request row
--      LANDS, so it looks like the interesting position).  *** RED ***
--      `LiveCSRow.agda:1313.65-67: error: [UnequalTerms] (…csCnxt blkA l d
--      …CScPos.ccIdle (ApiCSCar sendCSRequestNext , …apiCS l d …sendCSRequestNext) v |
--      l Data.Fin.Properties.≟ l | (DecEq-Dir DecEq.≟ d) d) != nothing of type (Maybe
--      NS.CScPos) when checking that the expression eq has type nothing ≡ just _x`.
--      What it establishes: the pin's SOURCE half is a real table reading and not a
--      restatement — `ccIdle` is the one position whose `sendCSRequestNext` entry is a
--      `just`, and the error prints that entry's two unresolved key gates.
--
-- *** RE-AIMING NOTES FOR WHATEVER COMES AFTER THIS SLICE. ***  F66 is aimed at the
-- SHARPENING's vacuous arm: if a successor ever makes `CscCliFired`'s pin
-- direction-free (a tag-and-link-only pin, say), F66 stops guarding anything and the
-- honest record is the T7 rule's "no funded clause left to guard".  F67 is aimed at
-- ONE of six sibling clauses; if `cliDrvAdj-c01` is ever merged with `-c56` into a
-- per-tag dispatch, re-aim F67 at the merged clause rather than deleting it.  F69's
-- target is `cscReqEdge`; `cscRfwEdge` and `cscDoneEdge` are the SAME twelve clauses
-- at the other two keys and are deliberately NOT guarded separately (one guard per
-- FAMILY, this file's standing rule) — but if either grows a value gate of its own,
-- it becomes a new family and wants its own.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §8  (T8c-ii) *** THE CARRY AND THE DISCHARGE — WHAT IS LEFT, AND THE ROUTE.
-- Read this before touching `LiveChanJoin` or `LiveRelayCS` §1. ***
--
-- *** WHAT IS DONE. ***  `dnFresh⇒areq` is now premise-free except for its carried
-- arguments: all THREE `⊥`-premises are theorems (`LiveSrvOpen` §6 —
-- `cellDrainCS-⊥`, `cellReqCS-⊥`, `cliWreqCS-⊥`, on the two io ladders
-- `LiveIoIntroCS` §1c/§2b landed), `CliDrvAdj` has a TOTAL producer (§6c) off the
-- bundle sharpening (`LiveLegApiCone` §2b⁵), and both state-level classes are proved
-- (§5b's nine, §5c's three).  So the object is complete and USABLE; what is missing
-- is only that nothing CARRIES it yet, and therefore nothing consumes it.
--
-- *** WHAT IS LEFT, in the order it has to happen. ***
--
--   (i) THE CARRY.  `DnFresh` and `DrvCliD` must become part of the FSim `Rel`'s
--       per-leg invariant, i.e. a trailing factor of `LiveChanJoin.LegJointU`.
--       *** CARRY THEM AS ONE FACTOR, NOT TWO: *** define
--       `DnJoint l s = DnFresh l s × DrvCliD l s` here, join `DnJoint` as
--       `LegJointU`'s SEVENTH factor, and give it one selector.  Then each of
--       `LiveChanJoin` §6's FIVE arms gains exactly ONE argument, which halves the
--       join-level plumbing — and the two halves always move together anyway, because
--       every step class that moves one moves the other.
--
--       The five per-class carry lemmas, with the ingredients each needs (all of
--       them already exist; none needs a new cone field):
--         · MEDIUM τ (`τpreserveU-med`) — dispatch on the drained key exactly as
--           `LiveChanJoinCS.chanCSLeg-drain` does: at the leg's own dn CS key use
--           `dnFresh-drainS` (the `draining y → empty` class) and `drvCliD-frame`;
--           at any other key `dnFresh-frame` + `drvCliD-frame`.  `drainSucc` keeps
--           all four node records LITERAL, so the relay's phase, the two CS
--           positions and node D's phase are `refl`.
--         · `break` (`evStepU-break`) — frame both.  A `break` moves `broken` only.
--         · VISIBLE api (`evStepU-api`) — *** THE COST CENTRE, and the one place the
--           WHICH-NODE-FIRED dispatch is needed (the fix-round review's I-4). ***
--           Read `deRelayAdvBD`/`-CD`: the fixity half gives `relayOf l s ≡ relayOf
--           l s′` and then the other three components decide (node D fired ⇒
--           `dnFresh-nodeDApi` + `drvCliD-api` off §6c's `cliDrvAdj-of`, fed by
--           `deConsStep*` and `deCsCli*`; a relay or node A fired ⇒ frame, with node
--           D's slots literal); the FIRED half goes to `relayAdv-guard` and then to
--           `dnFresh-relayCons` (source-in-region, which needs the FOUR component
--           fixities — see the note at that lemma for where each comes from) or
--           `dnFresh-relayOut` (successor-outside, which needs nothing).  For
--           `DrvCliD` on a relay-fired step the class is `drvCliD-frame`.
--         · io FILL (`tauIoU-in`) — dispatch on the filled key: at the leg's dn CS
--           key the peer that fired is either the dn CS SERVER (`dnFresh-srvSendS`)
--           or node D's CLIENT (`dnFresh-cliSendS` + `drvCliD-send`), which the io
--           cone's CS row slots decide; elsewhere frame both.
--         · io READ (`tauIoU-out`) — the same shape at `dnFresh-srvReadS` /
--           `dnFresh-cliReadS` + `drvCliD-read`.
--
--   (i-b) *** THE OBLIGATION T8c-ii FOUND, AND THE FIX IT PROPOSED — WHICH IS
--       REFUTED.  T8c-iii's first slice; both halves recorded because the refutation
--       is the more useful half. ***
--
--       WHAT T8c-ii FOUND (and it was right): two independent fixity-or-fired
--       disjunctions are unusable at this consumer.  At node D's `cp0 → cp1` hop the
--       api carry holds the driver's step and must produce `CliAt cp1 (dnCScC l s′)`;
--       if the sharpening's field reads `inj₁`, the client is reported FIXED at
--       `ccIdle` while its own driver fired `sendCSRequestNext` — the very state the
--       sharpening excludes, so excluding it needs the sharpening.  CIRCULAR.
--
--       WHAT T8c-ii PROPOSED, AND WHY IT IS FALSE: "make the two fields UNCONDITIONAL
--       `CscCliFired`, at the cost of two key-refutation OUT maps".  *** The
--       unconditional field is not dearer, it is UNPROVABLE. ***  `CsAt` is
--       tag-GENERIC and node B's own CS SERVER sits at the SAME KEY as node D's CS
--       client — node B's BD bundle is `absBundleG linkBD lo hi` (`SysStep:770`), node
--       D's is `absBundleG linkBD hi lo` (`:781`), so both peers key on
--       `(linkBD , hi)`.  When node B's server fires `apiCS linkBD hi reqCSRequestNext`
--       (`NodeSpecs.csSnxt:428`) the pin HOLDS, node D's client is untouched, and
--       `csCnxt` has no `reqCSRequestNext` row at all, so the demanded row does not
--       exist.  Tag-SCOPING the pin would restore truth (the two peers' `apiCS` tag
--       sets are disjoint — `sendCSRequestNext` occurs only in `csCnxt`), but then the
--       four non-node-D arms have to refute a tag-scoped pin at a key they SHARE,
--       which needs a per-node tag-refusal family nobody has.
--
--       WHAT LANDED INSTEAD (T8c-iii, and it is ~20 lines rather than ~40 or ~250):
--       express the TRUE dichotomy — either node D's leg is entirely untouched, driver
--       AND client, or node D fired it and the step and the sharpening travel
--       TOGETHER.  `DriverExposed⁺.deConsStep*` and `deCsCli*` are merged into ONE
--       field per leg, `deNodeDBD`/`deNodeDCD`; every arm can supply it and the
--       consumer's dispatch is total on the pair.  See the note at that field.
--
--   (i-c) *** AND THE SAME SHAPE OF GAP EXISTS ON THE RELAY's SIDE — found the same
--       way, and NOT yet closed. ***  The api dispatch's other branch needs "the dn CS
--       server is FIXED across the relay's UP-link consume hops".  `deCsDrvBD`'s
--       `inj₁` gives it (its fixity half is the PAIR relay-phase × dn-CS-server), but
--       its `inj₂` half is two conditionals on the SUCCESSOR phase, both vacuous at a
--       `raCons` hop — so the datum is absent exactly where it is needed.  Without it
--       `dnFresh-relayCons`'s four-fixity precondition cannot be met, and the offending
--       combination (relay phase fixed, dn CS server moved by `saReq`) is IMPOSSIBLE in
--       every arm yet PERMITTED by the record — T8c-ii's defect, one peer over.
--       THE FIX, same shape: one further `DriverExposed⁺` field carrying
--       `(csS-BD fixed) ⊎ (the successor is `producing b q` with `q ≢ pp0`)` — the
--       honest dichotomy the fix round already banked ("every DOWN-link relay advance
--       lands outside the guard, every UP-link one has its source in the consuming
--       half"), with the second disjunct bridged to `RelayFresh … → ⊥` here.  ≈24, and
--       it must NOT be done by widening `DnCsDrv`: that type is consumed by
--       `LiveDrvBF.drvBF-api` and widening it drags that proof along.
--  (ii) THE RELAY `DrvCp` CLAUSES AND THE DISCHARGE.  With `DnJoint` carried,
--       `LiveRelayCS` §3's `coAt-split-at` can prove its `cp6` and `pp0` clauses by
--       `dnFresh⇒areq`, and `LiveRelayCS` §1's `CSAt` clauses become `⊤` — the
--       T1/T5/T6d/T7 pattern, fifth and sixth discharges, `csRes` RETIRED and
--       `Premises` down to `{cellCp3, bfRes}`.  (T10: `bfRes` shrank again — ONE
--       equation, `pp3`, since the `cp4` arm was discharged off `LiveDrvBFA.UpJoint`;
--       T11h discharged `pp3` itself off the carried `LiveDrvBFD.BFFresh` and T12
--       RETIRED the field, so `Premises = {cellCp3}` ALONE; and the cellCp3 window
--       discharged `cellCp3` itself off the carried join, so `Premises = {}`.)
--       *** AND ONE DEBT THIS DISCHARGE INCURRED, PAID IN T10's FIX ROUND. ***  Emptying
--       the CS half retired `LiveRelayCS`'s F48 — a vacuity guard whose target was
--       `CSAt`'s `cp6` clause — WITHOUT re-aiming it, so the CS axis went from T8c-iii to
--       T10 with no live vacuity guard while F48's own green record stayed in the file.
--       `LiveRelayCS` F92 is the re-aim (at `Sharp`'s `cp6` clause, the axis's one
--       remaining funded object), and the re-aiming rule gained the clause this miss
--       shows it needed: a discharge that empties a half's LAST funded clause moves the
--       guard to whatever object still carries a funded requirement, or the half records
--       that it has none.
--
--       *** THE PREMISE COUNT IS THE DECISION THE T8 REVIEW PRICED, and this is the
--       shape to use. ***  `dnFresh⇒areq` wants FIVE things `coAt-split-at` does not
--       have: the leg's dn-link unbrokenness, `isStable`, and the three `⊥`-premises
--       (now theorems, but each still needs the unbrokenness and the stability).  Do
--       NOT add five premises — that is the third-unconditional-premise trigger §3's
--       own note names.  Add ONE record instead (option (3), ≈10-20): a two-field
--       `CsIdleExcl l r` carrying `broken (med (toSys r)) (dnLink l) ≡ false` and
--       `isStable (radec r ∖ hidden blkA)`, and derive the three `⊥`-premises inside
--       the `cp6`/`pp0` clauses from `LiveSrvOpen` §6.  Every consumer of
--       `coAt-split-at` already holds both fields (the window's `wLink2` and the arm's
--       own stability), exactly as they hold the two `bsWsb`/`csWar` refutations.
--
-- *** THE ONE MEASURED WARNING. ***  This slice cost 622 net against a 410-810 band,
-- and 405 of it was item (2) — the two io ladders the T8 gate declared UNBUILT
-- without pricing them (366 lines in `LiveIoIntroCS` alone).  The carry above prices
-- at ≈250 and the discharge at ≈80 by inspection, so completing T8c-ii's original
-- scope in one task would have landed at ≈950 against a STOP of 900.  *** That is why
-- this file stops here with the object complete rather than with the carry half-built:
-- the campaign's own rule. ***  Price the remainder as its own task.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §9  (T8c-iii) *** THE CARRIED OBJECT AND THE PIECES THE JOIN NEEDS. ***
--
-- `LiveChanJoin` carries ONE factor, not two: `DnJoint` pairs the freshness clause
-- with node D's coupling, because every step class that moves one moves the other and
-- pairing halves the join-level plumbing (five arms × one argument instead of two).
-- The per-class work is NOT here — `mkDnJoint` lets the join compose §5b's nine
-- wrappers with §5c's three directly, so this section is only what those wrappers
-- cannot express:
--
--   · `relayFresh-prod-nz`, which turns the cone's "the successor is `producing bb qq`
--     with `qq ≢ pp0`" into `dnFresh-relayOut`'s premise;
--   · `cssRowP-noLink`, which turns "the label is on the leg's UP link" into the dn CS
--     SERVER's FIXITY — the datum `dnFresh-relayCons`'s four-fixity precondition was
--     missing, and the reason `DriverExposed⁺.deRelayBD` exists;
--   · `dnFresh-relayConsApi`, the one COMBINED class: the relay advanced inside the
--     region AND node D fired.  That combination is impossible in fact and not
--     refutable from the record, so it is CARRIED rather than excluded — cheaper than
--     a refutation and it keeps the join's dispatch total.
------------------------------------------------------------------------

-- *** NO PRODUCE SUCCESSOR BUT `pp0` IS IN THE REGION. ***  the bridge from the cone's
-- nineteenth component to `dnFresh-relayOut`'s premise
relayFresh-prod-nz : (b : Block₃) (q : ProdPh) → (q ≡ pp0 → ⊥)
                   → RelayFresh (producing b q) → ⊥
relayFresh-prod-nz b pp0 nz _ = nz refl
relayFresh-prod-nz b pp1 nz ()
relayFresh-prod-nz b pp2 nz ()
relayFresh-prod-nz b pp3 nz ()
relayFresh-prod-nz b pp4 nz ()
relayFresh-prod-nz b pp5 nz ()
relayFresh-prod-nz b pp6 nz ()
relayFresh-prod-nz b pp7 nz ()
relayFresh-prod-nz b pp8 nz ()
relayFresh-prod-nz b pp9 nz ()

-- *** A CS SERVER WHOSE KEY'S LINK IS NOT THE FIRED ONE DID NOT MOVE. ***  The
-- dispatch is on the `ApiHasLink` WITNESS and not on the label — nine constructors
-- instead of twenty-eight, and matching the witness is what makes the label-directed
-- `CSsApiRowP` reduce.  Seven of the nine land on its catch-all, which IS the fixity;
-- the two that carry a row (`apiCS`, and `done` on the ChainSync id) have `l₀ ≡ k` in
-- the row and the fired link in the witness, so the disequality closes them
cssRowP-noLink : (k : Link) (kd : Dir) (pos pos′ : SN.CSsPos)
    {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) {l₁ : Link}
  → ApiHasLink l₁ e → (l₁ ≡ k → ⊥)
  → CSsApiRowP k kd pos pos′ e a → pos ≡ pos′
-- the TWO labels a CS server has a row at: its own api channel and the ChainSync
-- `done` handshake.  Both carry `l₀ ≡ k` in the row, and the witness pins `l₀` to the
-- FIRED link, so the disequality closes them
cssRowP-noLink k kd pos pos′ (apiCS l₀ d₀ m) a ahlCS ne (inj₁ eq) = eq
cssRowP-noLink k kd pos pos′ (apiCS l₀ d₀ m) a ahlCS ne (inj₂ (leq , _ , _)) =
  ⊥-elim (ne leq)
cssRowP-noLink k kd pos pos′ (done l₀ d₀ N2N_ChainSync) a ahlDone ne (inj₁ eq) = eq
cssRowP-noLink k kd pos pos′ (done l₀ d₀ N2N_ChainSync) a ahlDone ne (inj₂ (leq , _ , _)) =
  ⊥-elim (ne leq)
-- every other label: `CSsApiRowP`'s catch-all IS the fixity, so the fact is returned
-- unchanged and the disequality is never read
cssRowP-noLink k kd pos pos′ (done l₀ d₀ N2N_BlockFetch)   a ahlDone ne h = h
cssRowP-noLink k kd pos pos′ (done l₀ d₀ N2N_KeepAlive)    a ahlDone ne h = h
cssRowP-noLink k kd pos pos′ (done l₀ d₀ N2N_TxSubmission) a ahlDone ne h = h
cssRowP-noLink k kd pos pos′ (done l₀ d₀ N2N_LeiosNotify)  a ahlDone ne h = h
cssRowP-noLink k kd pos pos′ (done l₀ d₀ N2N_LeiosFetch)   a ahlDone ne h = h
cssRowP-noLink k kd pos pos′ (input  l₀ d₀ i) a ahlIn  ne h = h
cssRowP-noLink k kd pos pos′ (output l₀ d₀ i) a ahlOut ne h = h
cssRowP-noLink k kd pos pos′ (apiBF l₀ d₀ m)  a ahlBF  ne h = h
cssRowP-noLink k kd pos pos′ (apiKA l₀ d₀ m)  a ahlKA  ne h = h
cssRowP-noLink k kd pos pos′ (apiTS l₀ d₀ m)  a ahlTS  ne h = h
cssRowP-noLink k kd pos pos′ (apiLN l₀ d₀ m)  a ahlLN  ne h = h
cssRowP-noLink k kd pos pos′ (apiLF l₀ d₀ m)  a ahlLF  ne h = h
-- … and the seven labels `ApiHasLink` has NO witness for: the argument is absurd
cssRowP-noLink k kd pos pos′ (sndmsg l₀ d₀ i) a () ne h
cssRowP-noLink k kd pos pos′ (rcvmsg l₀ d₀ i) a () ne h
cssRowP-noLink k kd pos pos′ (tx     l₀ d₀ i) a () ne h
cssRowP-noLink k kd pos pos′ (sndack l₀ d₀ i) a () ne h
cssRowP-noLink k kd pos pos′ (rcvack l₀ d₀ i) a () ne h
cssRowP-noLink k kd pos pos′ (ack    l₀ d₀ i) a () ne h
cssRowP-noLink k kd pos pos′ (store l₀ d₀ i) a () ne h
cssRowP-noLink k kd pos pos′ (env l₀ d₀ i) a () ne h
cssRowP-noLink k kd pos pos′ (break  l₀)      a () ne h

-- *** THE COMBINED CLASS: the relay advanced INSIDE the region and node D fired. ***
-- `dnFresh-relayCons` wants node D's two slots FIXED; when node D moved instead, its
-- own api class supplies them.  The two are about DISJOINT components, so composing is
-- sound — and it is what keeps the join's api dispatch total over a combination that
-- cannot happen but that the record permits (§8 (i-b)'s lesson, applied rather than
-- re-learned)
dnFresh-relayConsApi : (l : TwoLegs) (s s′ : SysState) (b : Block₃) (c : ConsPh)
                     → relayOf l s ≡ consuming b c
                     → dnCSsOf l s ≡ dnCSsOf l s′
                     → cellCSDn l s ≡ cellCSDn l s′
                     → CliDrvAdj (dnCScC l s) (phOf l s) (dnCScC l s′) (phOf l s′)
                     → DnFresh l s → DnFresh l s′
dnFresh-relayConsApi l s s′ b c req seq heq adj fr _ =
  dnFresh-cliApi _ _ _ _ _ _ adj
    (dnFreshC-cong _ _ _ _ _ _ _ _ (cong SStep.coarsenCSs seq) heq refl refl
      (fr (subst RelayFresh (sym req) tt)))

-- *** THE CARRIED PAIR. ***  node D's freshness clause and node D's coupling, joined
-- as ONE `LegJointU` factor
-- *** (T11e) A THIRD HALF: §6h's `{pp2, pp3}` RECORD JOINS THIS FACTOR RATHER THAN
-- BECOMING A NEW ONE. ***  It walks the SAME down-ChainSync hop, reads the SAME
-- adjacencies, and every datum its classes want is already bound at each of
-- `LiveChanJoin`'s seven `mkDnJoint` sites — so folding it in costs ONE component per
-- site, where a trailing `LegJointU` factor would have cost this factor's whole
-- 402-line arm set a second time (T11d's measurement).  *** Appending a factor is
-- cheap only when someone else already walks its hop; here someone does. ***
DnJoint : TwoLegs → SysState → Set
DnJoint l s = DnFresh l s × DrvCliD l s × DnRfw l s

-- BASE — all three halves at `initial`
dnJoint-init : (l : TwoLegs) → DnJoint l initial
dnJoint-init l = dnFresh-init l , drvCliD-init l , dnRfw-init l

-- … and the ONE combinator the join needs: every step class is a TRIPLE of the classes
-- §5b, §5c and §6i already prove, so no per-class pairing lemma is written here
-- *** (T11e) THE THIRD CLASS FUNCTION READS THE SECOND, and it has to: *** the
-- keystone (`dnRfw-enter`) REBUILDS the record at the successor and its ORDER FACT
-- comes off `DrvCliD` there — so the api arm needs the coupling's own successor,
-- which only this combinator can hand it.  The other six classes ignore the argument.
mkDnJoint : (l : TwoLegs) (s s′ : SysState)
          → (DnFresh l s → DnFresh l s′) → (DrvCliD l s → DrvCliD l s′)
          → (DrvCliD l s → DnRfw l s → DnRfw l s′)
          → DnJoint l s → DnJoint l s′
mkDnJoint l s s′ f g h (fr , cpl , rfw) = f fr , g cpl , h cpl rfw

-- the two projections, for a consumer that wants one half (the arms want `DnFresh`
-- and `DrvCliD` separately — `dnFresh⇒areq` takes both)
dnJoint⇒fresh : (l : TwoLegs) (s : SysState) → DnJoint l s → DnFresh l s
dnJoint⇒fresh l s (fr , _) = fr

dnJoint⇒cpl : (l : TwoLegs) (s : SysState) → DnJoint l s → DrvCliD l s
dnJoint⇒cpl l s (_ , cpl , _) = cpl

-- (T11e) … and the third, which is what the `pp3` arm's discharge reads
dnJoint⇒rfw : (l : TwoLegs) (s : SysState) → DnJoint l s → DnRfw l s
dnJoint⇒rfw l s (_ , _ , rfw) = rfw

------------------------------------------------------------------------
-- §7e  (T8c-iii) THE THREE GUARDS THIS RANGE's NOVEL OBJECTS OWE — the merged
-- fields, the classifier's nineteenth component, and the OUT map.  All
-- arity-preserving, all RUN, all RED, all reverted by STRING INVERSION with
-- `git status` verified clean after each.  Line numbers are as-run at `9744a50`.
--
-- (F74  *** THE MERGED FIELD's LEG — F65's mutation at the shape that replaced the
--      two fields F64/F65/F68 guarded. ***)  In `nodeD-api-BD-evo⁺`'s record, report
--      leg BD's step-and-sharpening PAIR as leg CD's and CD's fixity pair as BD's.
--      Arity-preserving (the two fields have the same shape) and it is the mutation
--      the merge itself invites, since one field now carries what two used to.
--      *** RED ***  `LiveLegApiExpose.agda:1342.35-40: error:
--      [MismatchedProjectionsError] The projections …NodeStateD.cons-CD and
--      …NodeStateD.cons-BD do not match when checking that the expression cCDeq has
--      type SN.cons-BD nd′ ≡ SN.cons-BD (nD s)`.  What it establishes: *** the
--      merge did not weaken the leg pinning *** — the fixity half still names the
--      CO-leg's own slot by projection, so a cross-wired arm cannot typecheck.  Same
--      error CLASS as F65's, which is the point: the guard survived the reshape
--      rather than needing a new one.
--
-- (F75  *** THE NINETEENTH COMPONENT's LOAD-BEARING HALF. ***)  In
--      `cpStepKindQ-of⁺`'s `cp6` clause, answer the new component with `pp0` in place
--      of `pp1` — i.e. claim the bind hop's successor is INSIDE the freshness region.
--      Arity-preserving, and it is exactly the claim the component exists to deny.
--      *** RED ***  `LiveLegApiCone.agda:2728.40-44: error: [UnequalTerms] pp1 != pp0
--      of type ProdPh when checking that the expression refl has type producing b pp1
--      ≡ producing b pp0`.  What it establishes: the component's second disjunct is a
--      real statement about the successor and not a formality — the `cp6` hop's
--      landing is `pp1`, outside the region, which is what makes the api carry's
--      relay branch discharge by `dnFresh-relayOut` rather than by four fixities.
--
-- (F76  *** THE OUT MAP's LINK EQUATION, AND ITS DIRECTION. ***)  In
--      `cssRowP-noLink`'s `apiCS` row clause, refute with `sym leq` instead of `leq`.
--      Arity-preserving, and `sym` is added reflexively all over this file.
--      *** RED ***  `LiveDrvCSD.agda:2564.19-22: error: [UnequalTerms] l₀ != k of
--      type (Data.Fin.Base.Fin (Params.numLinks p)) when checking that the expression
--      leq has type k ≡ l₀`.  What it establishes: the two link facts enter from
--      OPPOSITE ends — the `ApiHasLink` witness pins the FIRED link to `l₀` and the
--      row pins the peer's KEY to `k` — so only one orientation composes with the
--      disequality.  The map is a genuine composition of the two and not a restatement
--      of either.
--
-- *** RE-AIMING NOTES. ***  F74 dies only if the two node-D fields are ever split
-- again (they should not be — §8 (i-b) says why); F75 dies if the nineteenth component
-- is ever restated without a successor claim, in which case the api carry's relay
-- branch has lost its `dnFresh-relayOut` route and wants re-planning, not a new guard;
-- F76 dies if `cssRowP-noLink` is ever generalised past the CS server (its BF twin
-- would be a new family and want its own).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7f  (T9) THE FAMILY's BLOCKFETCH MEMBER — ONE GUARD, at its own novelty.
--
-- (F82  *** THE OFFERING PHASE IS LOAD-BEARING. ***)  In `consDVis-brr-off`'s `cp2`
--      clause, claim the map is `nothing` there too — `consDVis-brr-off l b cp2 rg _
--      = refl` in place of `⊥-elim (no refl)`.  Arity-preserving (the premise stays
--      in the telescope and is ignored), and it is the mutation a reader who thinks
--      "the driver never offers a BlockFetch request" would write.
--      *** RED ***  `LiveDrvCSD.agda:1874.34-38: error: [UnequalTerms] … !=
--      nothing of type Data.Maybe.Maybe (PTree …) when checking that the expression
--      refl has type viewV (PTree.force (decConsD l (consD b cp2))) (ApiBFCar
--      sendBFRequestRange , apiBF l hi sendBFRequestRange) rg ≡ nothing`, and the
--      printed non-`nothing` side is the `Output-cont` head carrying `apiBF l hi
--      sendBFRequestRange` at `chainRange (point b) (point b)` — i.e. the error
--      EXHIBITS the offer.  What it establishes: `cp2` is the unique offering phase
--      and the exclusion premise is not decoration; the six `refl`/`rewrite` clauses
--      are a genuine per-phase computation, not a catch-all that happens to close.
--
-- *** RE-AIMING NOTE. ***  F82 dies if `consume-k`'s head ever stops being the
-- BlockFetch request (i.e. if the client chain is reordered), in which case the
-- offering phase moves and BOTH the member and `LiveRelayCS` §5b's inventory want
-- re-deriving rather than a new guard — the inventory's `cp0`/`cp1`/`cp2` split is a
-- consequence of the chain's order and of nothing else.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7g  (T11) THE TWO api-SYNC MEMBERS' OWN GUARD — ONE, at §6e's novelty (an
-- OUTPUT-prefix driver offer, which §3's and §6f's are not).  Arity-preserving,
-- RUN, RED at the predicted site, reverted by string inversion with `git diff`
-- verified clean.
--
-- (F96  *** THE `cp2` OFFER's LANDING. ***)  `consVis-cp2` states its successor
--      as `decCons l hi b₀ cp2` — itself — instead of `cp3`, i.e. the reading
--      under which the driver's own request emit would not advance it.  This is
--      the mutation a transcriber of §3's `consVis-cp0` would make, since there
--      the source and target phases differ by the same one step and the eye reads
--      the phase off the left-hand side.
--      *** RED ***: `LiveDrvCSD.agda:1986.53-57: [UnequalTerms] CSP.Operators.Prefix
--      … (apiBF l hi recvBFBlock) (λ b′ → CSP.Operators.Output … (apiBF l hi
--      sendBFClientDone) U.tt …) != …`, EXIT=42.  *** THE ERROR EXHIBITS THE TRUE
--      SUCCESSOR *** — the `recvBFBlock` prefix that IS `decCons … cp3` — so the
--      landing is pinned by the decode table and not by the lemma's own claim.
--      Re-aiming note: F96 dies if `consume-k`'s event order ever changes, at which
--      point the whole of §6d/§6e/§6f must be re-derived against the new order (the
--      KEEP-IN-SYNC marker at `LiveDrvBFD.BFCliDrvAdj` says the same thing for the
--      joint adjacency).
--
-- §6f needs no guard of its own beyond this one: its rung 1 is the SAME shape at
-- the value-gated peer row, and its own landing is returned EXISTENTIALLY (there
-- is no successor claim to mutate).  What would guard it is a mutation of the
-- PEER's row, and that is `ceqCSc15`'s, i.e. the oracle's rather than this file's.
------------------------------------------------------------------------

-- *** (T11e) THE GUARD's TWO-WAY SPLIT AT A STATE — the review's `relayRfw-cases`,
-- landed at last. ***  T11b took the token projection by refuting the OTHER two relay
-- constraints and declared the deviation; the api arm needs the PHASES themselves, so
-- the twelve-clause dispatch lands here after all — and it is twelve lines
relayRfw-cases : (x : CPPh) → RelayRfw x
               → (Σ[ b ∈ Block₃ ] x ≡ producing b pp2)
                 ⊎ (Σ[ b ∈ Block₃ ] x ≡ producing b pp3)
relayRfw-cases (consuming b y)   ()
relayRfw-cases (producing b pp0) ()
relayRfw-cases (producing b pp1) ()
relayRfw-cases (producing b pp2) _ = inj₁ (b , refl)
relayRfw-cases (producing b pp3) _ = inj₂ (b , refl)
relayRfw-cases (producing b pp4) ()
relayRfw-cases (producing b pp5) ()
relayRfw-cases (producing b pp6) ()
relayRfw-cases (producing b pp7) ()
relayRfw-cases (producing b pp8) ()
relayRfw-cases (producing b pp9) ()

-- *** (T11e) A HOP THAT LANDS AT `pp3` CAME OUT OF `pp2`. ***  `relayAdv-cp4`'s shape
-- at the arm's own sub-phase, and it is what (T11c)'s FOURTH `DnCsDrv` member is FOR:
-- the api arm holds the successor's phase and needs the source's
relayAdv-into-pp3 : {x x′ : CPPh} (b : Block₃) → RelayAdv x x′
                  → x′ ≡ producing b pp3 → x ≡ producing b pp2
relayAdv-into-pp3 b (raCons _ _ _ _ _)   ()
relayAdv-into-pp3 b (raCp6 _)            ()
relayAdv-into-pp3 b (raProd _ _ _ a01)   ()
relayAdv-into-pp3 b (raProd _ _ _ a12)   ()
relayAdv-into-pp3 b (raProd b₀ _ _ a23) refl = refl
relayAdv-into-pp3 b (raProd _ _ _ a34)   ()
relayAdv-into-pp3 b (raProd _ _ _ a45)   ()
relayAdv-into-pp3 b (raProd _ _ _ a56)   ()
relayAdv-into-pp3 b (raProd _ _ _ a67)   ()
relayAdv-into-pp3 b (raProd _ _ _ a78)   ()
relayAdv-into-pp3 b (raProd _ _ _ a89)   ()

-- *** (T11e) THE IN-GUARD ADVANCE WHEN NODE D MOVED IN THE SAME SYNC. ***  The two
-- classes are INDEPENDENT — `dnRfw-cliApi` moves `ca`/`x` at fixed `rx`, and
-- `dnRfw-relayAdv` moves `sa`/`rx` at fixed `ca`/`x` — so they COMPOSE, and the
-- composite is what the api arm calls on the cone's *node-D-fired* arm.  (The
-- alternative, refuting the combination, would need the label: node D's driver never
-- offers `sendCSRollForward`, but the api arm holds the phases and not the event.)
dnRfw-relayAdvJ : (l : TwoLegs) (s s′ : SysState) (b : Block₃) (ht : Header × Tip)
                → relayOf l s ≡ producing b pp2
                → relayOf l s′ ≡ producing b pp3
                → SStep.coarsenCSs (dnCSsOf l s′) ≡ NS.csWrf ht
                → cellCSDn l s ≡ cellCSDn l s′
                → InCp03 (phOf l s)
                → CliDrvAdj (dnCScC l s) (phOf l s) (dnCScC l s′) (phOf l s′)
                → DnRfw l s → DnRfw l s′
dnRfw-relayAdvJ l s s′ b ht peq peq′ hwf heq tk adj rw _ =
  dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl refl refl refl (sym peq′)
    (dnRfw-relayAdv b _ _ _ _ _ ht hwf
      (dnRfw-cliApi (producing b pp2) _ _ _ _ _ _ tk adj
        (dnRfwC-cong _ _ _ _ _ _ _ _ _ _ refl heq refl refl peq
          (rw (subst RelayRfw (sym peq) tt)))))

-- *** THE ACCEPTANCE PROBE FOR ITEM C, KEPT rather than thrown away — it is the glue
-- the ninth `LegJointU` factor's relay arm calls. ***  The cone's `pp3` landing
-- (`LiveLegApiCone.DnCsRfwLand`, T11b's own cone edit) is EXACTLY the hypothesis the
-- in-guard advance wants: applied at the arm's own successor phase it yields the
-- `Header × Tip` pair and the server's landed position, and nothing else is needed.
-- Green FIRST TRY at ≈21s.
--
-- The LINK is a parameter because the cone states the landing at a link and this
-- module has no `dnLink` accessor (`LiveRelayOpen`'s lives above it); the landing's
-- own body never reads it, so the caller passes its own leg's down link
dnRfw-relayAdvC : (l : TwoLegs) (s s′ : SysState) (b : Block₃) (l₀ : Link)
                → relayOf l s ≡ producing b pp2
                → relayOf l s′ ≡ producing b pp3
                → DnCsRfwLand l₀ (dnCSsOf l s) (dnCSsOf l s′) (relayOf l s′)
                → cellCSDn l s ≡ cellCSDn l s′
                → dnCScOf l s ≡ dnCScOf l s′
                → phOf l s ≡ phOf l s′
                → DnRfw l s → DnRfw l s′
dnRfw-relayAdvC l s s′ b l₀ peq peq′ land heq keq deq =
  dnRfw-relayAdvS l s s′ b (proj₁ (land b peq′)) peq peq′ (proj₂ (land b peq′))
                  heq keq deq

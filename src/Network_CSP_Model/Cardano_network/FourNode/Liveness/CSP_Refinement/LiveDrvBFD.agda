{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- (T11) THE DOWN-HOP BLOCKFETCH FRESHNESS CLAUSE — `LiveDrvCSD`'s `DnFresh`
-- one PROTOCOL over, and the `pp3` arm's own invariant.
--
-- *** WHAT IT SAYS, IN ONE LINE: while the relay has not yet fired `reqBFRange`
-- on its down link, the leg's down BlockFetch hop has not yet started — the
-- server is at `bsIdle` or `bsAreq rg`, the client has at most its range request
-- outstanding, the cell holds at most that request, and node D's own consume
-- driver has not passed the request. ***
--
-- The arm this exists for is `LiveRelayCS.BFAt`'s `producing _ pp3` clause, the
-- LAST equation of the nine-arm api residual:
--
--     BFAt l s (producing _ pp3) = Σ[ rg ] (coarsenBFs (dnSrv l s) ≡ NS.bsAreq rg)
--
-- and the route is `LiveDrvCSD` §4-§5's exactly: carry a guarded four-conjunct
-- core plus a correlation, and let §3's sharpening turn it plus the caller's
-- stability refutations into the equation by REFUTING `bsIdle`.
--
-- *** READ §0 FIRST.  IT IS THE (T9/T10) GUARD CHECK, AND IT IS WHAT FIXES THIS
-- OBJECT'S SHAPE. ***  Two hazards were caught there BEFORE anything was built
-- (§0(5) and §0(6)), and one measured POSITIVE retired the cone work the
-- ChainSync twin had to pay for (§0(4)).
--
-- CONTENTS: §0 the guard check; §1 the regions, the core, its base and frame;
-- §2 the six step classes and node D's joint BF adjacency; §2b the state-level
-- wrappers; §3 the sharpening (the arm's own equation, `RState`-free).
--
-- No postulate, no hole, no `mutual`, no `with` in anything whose type mentions
-- an imported `blkA`-parameterised predicate.
------------------------------------------------------------------------

open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBFD
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
-- §0(4)'s row-degeneracy check is stated at an `apiCS` label, so the label's
-- constructor and its carrier family are both needed
open import CSP.Examples.Cardano_network.Net p
  -- (T11d) … and §2c's producer inverts node D's own step at each of its six heads,
  -- so the three `apiCS` tags of `consume`, the three `apiBF` ones, both carrier
  -- families and the decidable equality that unsticks the offer map all join
  using ( Net_Api; Net_Api-≟; Link; apiCS; ApiCSTag; ApiCSCar
        ; sendCSRequestNext; recvCSRollforward; sendCSDone
        ; apiBF; ApiBFTag; ApiBFCar
        ; sendBFRequestRange; recvBFBlock; sendBFClientDone )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; blockFetch; ChainRange; MessageBlockFetch
        ; MsgRequestRange; MsgStartBatch; MsgNoBlocks; MsgBlock
        ; MsgBatchDone; MsgClientDone )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi; Mode )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Time; Length )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA as SM
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              -- (T11d) node D's own driver, at the phase-indexed decode §2c inverts,
              -- and the FINE client position the cone's row facts are stated at
              ; ConsDPh; consD; decCons; decConsD; BFcPos
              -- the guard is a dispatch on the RELAY's phase, so all seventeen
              -- shapes are written out and every constructor is needed
              ; CPPh; consuming; producing
              ; ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9 )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  -- (T11d) … and the FINE client position §2c's producer is stated at (the cone's
  -- row facts are), beside the process type its step inversion names
  using ( coarsenBFs; coarsenBFc; NetProc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  -- node D's per-leg consume phase: the LANDED accessor, so this file adds none
  using ( TwoLegs; legBD; legCD; phOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ConsAdv; c01; c12; c23; c34; c45; c56
        ; ProdAdv; a01; a12; a23; a34; a45; a56; a67; a78; a89 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( relayOf; dnClient; cellDn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( dnSrv )
-- §0's guard dispatch runs on the cone's relay-advance relation, and §0(4) reads
-- the two BF api-row facts the cone reports at EVERY label
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiCone blkA
  -- (T11d) … and the two BF-CLIENT LANDINGS §2c's `cp2` and `cp3` clauses read: the
  -- `sendBFRequestRange` one is §2b⁷'s (built for this consumer) and the
  -- `recvBFBlock` one is T10's §2b′⁶, reused verbatim.  Both are bundle facts —
  -- `CliApiRowP`'s FIXITY arm is the case each one excludes
  using ( RelayAdv; raCons; raCp6; raProd; SrvApiRowP; CliApiRowP
        ; CliReqLand; CliRecvLand; BrrAt; RbbAt
        -- (T11h) … and the cone's own statement of this region's COMPLEMENT
        ; PastAreq )
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( Skip )
open import Level using ( 0ℓ )
import Relation.Nullary as RN
open import Process_Trees using ( ExtI )
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( ev; evl; evLabel; _─[_]─►_; sVis )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( nothing-absurd; bind-ev-inv )
-- the SIX BlockFetch step adjacencies, at COARSE positions: the landed
-- transcriptions of the two tables (`LiveChanInv` §4), so §2's calculus
-- transcribes no table of its own
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanInv blkA
  using ( SrvSendAdj; ssSB; ssNB; ssBlk; ssBD
        ; SrvReadAdj; srReq; srCD
        ; CliSendAdj; csReq; csCD
        ; CliReadAdj; crSB; crNB; crBlk; crBD
        ; rrPayload; nbPayload )
-- §0(3)'s contrast: the ChainSync twin's own guard, which is `⊥` at `pp3` where
-- this one is `⊤` (`LiveRelayCS` §5b(1) is the negative that made this module
-- necessary)
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvCSD blkA as LDC
-- (T11e) … and the FIFTH `LegJointU` factor, which §3's pair joins: `BFFresh` walks
-- the SAME down-BlockFetch hop, so it folds into `DrvBF` rather than trailing behind it
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBF blkA as LDB

------------------------------------------------------------------------
-- §0  *** THE GUARD CHECK — THE (T9/T10) MANDATORY FIRST STEP, DONE IN WRITING
-- AND MACHINE-CHECKED BEFORE ANY OF §1-§3 WAS WRITTEN. ***
--
-- The standing law (T9's lesson, T10's confirmation): *** a guarded invariant
-- transposes only as far as its GUARD does, so evaluate the guard region at the
-- arm's OWN sub-phase — and at the region's ENTERING STEP — before pricing or
-- building anything on it. ***  T9 spent the check on the CARRIED objects and
-- found `DnFresh` vacuous at `pp3`; this section spends it on the object about to
-- be BUILT, which is the other half of the same law.
--
-- THE REGION.  `RelayFreshBF` below is "the relay has not yet fired
-- `reqBFRange` on its down link" — the whole `consuming` half plus `producing _
-- {pp0 … pp3}`.  `produce`'s events are, in order, `reqCSRequestNext ·
-- sendCSAwaitReply · sendCSRollForward · reqBFRange · sendBFStartBatch · …`
-- (`FourNodeDiamond.lagda.md:199-208`), so the phase `producing _ ppN` is the
-- state in which the driver is ABOUT TO fire the (N+1)-th event: `pp3` is about
-- to fire `reqBFRange`, and `bfSnxt (bsAreq r) … reqBFRange ≡ just bsBusy`
-- (`NodeSpecs:596-600` — the T11 review's M-4 corrects this citation, which read
-- `:531-535`: those lines are `bfCnxt … bcWcd`, a different table and a different
-- peer role.  The FACT is unchanged and true: `bsAreq r` has exactly one genuine
-- row) is the only way off `bsAreq`.  Hence the region's last
-- member is `pp3` — the arm's own sub-phase.
--
-- (1) *** THE GUARD IS FREE AT THE ARM. ***  `relayFreshBF-pp3` below: `⊤` at
--     `producing _ pp3`, so a consumer never computes the guard.  This is the
--     EXACT CONTRAST with the ChainSync twin, whose guard is `⊥` there
--     (`LiveRelayCS.relayFresh-⊮-pp3`, T9) — and it is the whole reason this
--     object has to exist rather than `DnFresh` being reused.
--
-- (2) *** THE REGION SEPARATES `pp3` FROM `pp4`, WHICH IS WHAT MAKES THE OBJECT
--     PRESERVABLE AT ALL. ***  `relayFreshBF-⊮-pp4`: the relay's own
--     `reqBFRange` emit leaves the region, so the ONE step no sibling conjunct
--     could refute (the server's exit from `bsAreq`) is refuted by the guard.
--     This is `DnFresh`'s review-I-2 structure at the BlockFetch emit.
--
-- (3) *** THERE IS NO ENTERING STEP AT ALL, and that is a property of the phase
--     axis rather than a convenience. ***  The relay's advance relation
--     (`RelayAdv`) is `consuming cp0 → … → cp6 → producing pp1 → … → pp9` with
--     NO row back to `consuming` — `raCons`/`raCp6`/`raProd` are its three
--     families and `ProdAdv` stops at `a89`.  So the region is an INITIAL
--     SEGMENT of an acyclic chain that contains the initial phase, i.e. it is
--     backward-closed: a state inside it has every predecessor inside it too.
--     `relayAdvBF-guard` is that fact as a total dispatch, in
--     `LDC.relayAdv-guard`'s own shape.
--
-- (4) *** THE POSITIVE, AND IT IS MEASURED: THE FOUR IN-REGION RELAY ADVANCES
--     COST NO CONE WORK. ***  `DnFresh`'s guard has exactly ONE producing member
--     (`pp0`), so ALL of its down-link relay advances are vacuous
--     (`LDC.relayAdv-guard` answers `inj₂ (λ ())` at `raCp6` and at all nine
--     `raProd` rows).  This region has FOUR, so `raCp6` and `a01`/`a12`/`a23`
--     are advances whose SOURCE AND SUCCESSOR ARE BOTH INSIDE — a step class the
--     ChainSync twin never had to write, and the reason it needed
--     `LiveLegApiExpose.deRelayBD`'s third case (`qq ≡ pp0 → ⊥`, hard-wired to
--     ITS region).  *** ONE OF THE FOUR SITS ON AN UNREACHABLE SOURCE (T11 review's
--     M-7): `raCp6` lands at `producing b pp1` and the cone records that no visible
--     step ever lands at `pp0` (`LiveLegApiCone:2845-2848`), so `a01`'s source is
--     unoccupied and only THREE of the four are live steps.  Nothing here depends on
--     it — `relayAdvBF-guard` answers `inj₁ tt` regardless, and `DnFresh`'s producing
--     half is vacuous for the same reason — but the cost contrast is honestly
--     three-versus-nothing, not four-versus-one. ***  *** No such field is needed here: *** all four fire
--     `apiCS` events, and `srvRowP-apiCS`/`cliRowP-apiCS` below show that at a
--     non-BlockFetch label the cone's two BF row facts DEGENERATE TO THE FIXITY
--     EQUATION by definition (`SrvApiRowP`'s and `CliApiRowP`'s catch-all
--     clauses, `LiveLegApiCone:1140-1166` — re-derived at T12; the old
--     `:1026-1050` was ~100 lines stale before T11h moved the target 19 further).
--     With `deRowsBD`/`deRowsCD`'s two
--     components, `deMed` for the cell and `deNodeDBD`/`-CD`'s fixity arm for
--     node D's phase, every one of the four is a FRAME.
--
-- (5) *** THE FIRST HAZARD THE CHECK CAUGHT: the client region is NOT io-closed
--     on its own. ***  `crNB-row` below is the row `bcBusy + MsgNoBlocks →
--     bcIdle`: a client inside the region can be pushed BACK to `bcIdle` by a
--     wire read.  So a phase conjunct of the form "node D is pre-request" is
--     FALSE as an invariant unless the CELL conjunct forbids a `MsgNoBlocks`,
--     which it does (§1's `CellFreshBF` admits only the unread range request).
--     The region is closed only WITH the cell conjunct — `LiveDrvCSD` §4's
--     indivisibility argument, one protocol over, and it is why the four
--     conjuncts are again one object.
--
-- (6) *** THE SECOND HAZARD, AND IT DECIDED THE SHAPE OF THE PHASE CONJUNCT.
--     ***  A phase conjunct "node D is at `{cp0, cp1, cp2}`" would be FALSE:
--     node D fires `sendBFRequestRange` at `cp2` and the relay is still at `pp3`
--     afterwards (the relay's `pp2 → pp3` step is its own `sendCSRollForward`,
--     T9's pin finding), so `(pp3 , cp3)` is REACHABLE.  What IS true is the
--     JOINT statement "at `cp3` the client is past `bcIdle`" — so the conjunct
--     is `PhCli`, a dispatch on node D's phase whose `cp3` clause constrains the
--     CLIENT.  And the third face of the same hazard: `(cp4 , bcIdle)` satisfies
--     any phase-only conjunct while its own `sendBFClientDone` hop takes the
--     client OUT of the region, so `PhCli`'s `cp4`/`cp5`/`cp6` clauses are `⊥`
--     — true under the guard (reaching `cp4` needs `recvBFBlock`, hence a client
--     at `bcAblk`, which the client conjunct excludes) and it is what makes the
--     object supply `InCp03` itself instead of premising the token.
--
-- WHAT THE CHECK DID NOT MOVE: T9 §5b's four negatives and the `cp1` leaf.  The
-- leaf is still ChainSync-axis work and it is still this arm's whole risk; §3's
-- sixth premise is where it enters.
------------------------------------------------------------------------

-- *** THE GUARD: the relay has not yet fired `reqBFRange` on its down link. ***
-- Four producing members where `LDC.RelayFresh` has one — see §0(4) for what
-- that costs and §0(1) for what it buys.
--
-- *** KEEP IN SYNC WITH `LiveLegApiCone.PastAreq` (`:3770-3780`). ***  That predicate
-- is this one's COMPLEMENT on the producing phases, duplicated because the cone is
-- upstream of this module and cannot see `RelayFreshBF`.  A change to EITHER extent —
-- a phase flipped, or a new `ProdPh` constructor — must touch both.  *** THE DRIFT IS
-- MACHINE-CAUGHT, not merely documented: *** `pastAreq-⊮` below is exhaustive on
-- `ProdPh` in BOTH polarities (ten clauses, `()` on one side or the other, no
-- catch-all), so making any phase `⊤` in both, or flipping one alone, kills the
-- corresponding clause's absurd pattern and the module goes RED.  That is the keeper;
-- do not weaken it to a catch-all.
RelayFreshBF : CPPh → Set
RelayFreshBF (consuming b x)   = ⊤
RelayFreshBF (producing b pp0) = ⊤
RelayFreshBF (producing b pp1) = ⊤
RelayFreshBF (producing b pp2) = ⊤
RelayFreshBF (producing b pp3) = ⊤
RelayFreshBF (producing b pp4) = ⊥
RelayFreshBF (producing b pp5) = ⊥
RelayFreshBF (producing b pp6) = ⊥
RelayFreshBF (producing b pp7) = ⊥
RelayFreshBF (producing b pp8) = ⊥
RelayFreshBF (producing b pp9) = ⊥

-- §0(1) the guard AT THE ARM's own sub-phase — `⊤`, where the ChainSync twin's
-- is `⊥` (`LiveRelayCS.relayFresh-⊮-pp3`).  The one line the T9 lesson asks for
relayFreshBF-pp3 : (b : Block₃) → RelayFreshBF (producing b pp3)
relayFreshBF-pp3 b = tt

-- … and at the arm's own state, which is the form a consumer applies
relayFreshBF-at : (l : TwoLegs) (s : SysState) (b : Block₃)
                → relayOf l s ≡ producing b pp3 → RelayFreshBF (relayOf l s)
relayFreshBF-at l s b eq = subst RelayFreshBF (sym eq) tt

-- §0(2) … and the emit's own successor is OUTSIDE it: the step that takes the
-- server off `bsAreq` is refuted by the guard and by nothing else
relayFreshBF-⊮-pp4 : (b : Block₃) → RelayFreshBF (producing b pp4) → ⊥
relayFreshBF-⊮-pp4 b ()

-- §0(3) the region is BACKWARD-CLOSED: for every relay advance either the SOURCE
-- is inside (so the guard transports for free) or the SUCCESSOR is outside (so
-- the obligation is vacuous).  Total on `RelayAdv`, so no advance family is
-- missed — `LDC.relayAdv-guard`'s shape, with the SOURCE returned as a guard
-- rather than as a `consuming` witness, because here the in-region sources are
-- not all consuming ones (§0(4))
relayAdvBF-guard : (x x′ : CPPh) → RelayAdv x x′
                 → RelayFreshBF x ⊎ (RelayFreshBF x′ → ⊥)
relayAdvBF-guard _ _ (raCons b b′ c c′ _)  = inj₁ tt
relayAdvBF-guard _ _ (raCp6 _)             = inj₁ tt
relayAdvBF-guard _ _ (raProd _ _ _ a01)    = inj₁ tt
relayAdvBF-guard _ _ (raProd _ _ _ a12)    = inj₁ tt
relayAdvBF-guard _ _ (raProd _ _ _ a23)    = inj₁ tt
relayAdvBF-guard _ _ (raProd _ _ _ a34)    = inj₂ (λ ())
relayAdvBF-guard _ _ (raProd _ _ _ a45)    = inj₂ (λ ())
relayAdvBF-guard _ _ (raProd _ _ _ a56)    = inj₂ (λ ())
relayAdvBF-guard _ _ (raProd _ _ _ a67)    = inj₂ (λ ())
relayAdvBF-guard _ _ (raProd _ _ _ a78)    = inj₂ (λ ())
relayAdvBF-guard _ _ (raProd _ _ _ a89)    = inj₂ (λ ())

-- §0(4) THE FOUR IN-REGION ADVANCES, as the contrast that prices them: the
-- ChainSync guard is `⊥` at all four successors and this one is `⊤`, so these
-- are exactly the step classes the twin never had to write
inRegionBF-⊮-CS : (b : Block₃)
                → ((LDC.RelayFresh (producing b pp1) → ⊥) × RelayFreshBF (producing b pp1))
                × ((LDC.RelayFresh (producing b pp2) → ⊥) × RelayFreshBF (producing b pp2))
                × ((LDC.RelayFresh (producing b pp3) → ⊥) × RelayFreshBF (producing b pp3))
inRegionBF-⊮-CS b = ((λ ()) , tt) , ((λ ()) , tt) , ((λ ()) , tt)

-- … and the MEASURED positive that makes them free: at an `apiCS` label the
-- cone's BF SERVER row fact IS the fixity equation, by `SrvApiRowP`'s catch-all.
-- So the relay's three down-link ChainSync hops (and its `cp6` bind hop) hand
-- the down BF server's fixity over with no new cone component, no new
-- `DriverExposed⁺` field and no `BundleApiEvo` append
-- *** THE FINE POSITIONS ARE THE RIGHT ONES, and that is a bonus: *** the cone
-- states both row facts at `SN.BFsPos`/`SN.BFcPos` (its own `deRowsBD` reads the
-- node fields, `LiveLegApiExpose:794-797`), so what the four advances hand over
-- is the SLOT equation and `cong coarsenBFs` gives the coarse one — which is
-- what §2b's frame takes.  Measured: `NS.BFsPos !=< SN.BFsPos` at the first cut
-- *** THESE TWO ARE DEFINITIONAL CERTIFICATES, NOT UNSPENT CONVERTERS — DO NOT DELETE
-- THEM AS DEAD CODE. ***  Each body is the bare `h`, so each typechecks ONLY BECAUSE
-- `SrvApiRowP`/`CliApiRowP`'s CATCH-ALL clause makes the `apiCS` case the bare fixity
-- equation (`LiveLegApiCone:1140-1166`).  Add an `apiCS` clause to either row predicate
-- and these go RED — which is exactly the guard wanted, because the whole T11g/T11h
-- "that half is free" result rests on that catch-all, and so does `acsAt⇒srvFix`, the
-- `ApiCSAt` form spent three times at `dnSrvPre-dn`'s `pp1`/`pp2`/`pp3` clauses.  Having
-- no CONSUMER is the normal state of a certificate; it is not evidence of dead code.
-- (Recorded at the post-close fix round: T12's report had parked them as "consumer-free,
-- the same shape as the lemma just deleted".  Wrong on both counts — `acsAt⇒cliFix` was
-- an unspent CONVERTER for a route that was abandoned, and these certify a definitional
-- fact the tree depends on.)
srvRowP-apiCS : (k : Link) (kd : Dir) (bfs bfs′ : SN.BFsPos)
                (l₀ : Link) (d₀ : Dir) (m : ApiCSTag) (v : ApiCSCar m)
              → SrvApiRowP k kd bfs bfs′ (apiCS l₀ d₀ m) v → bfs ≡ bfs′
srvRowP-apiCS k kd bfs bfs′ l₀ d₀ m v h = h

-- … and node D's own BF CLIENT's, at the same label and for the same reason
cliRowP-apiCS : (k : Link) (kd : Dir) (bfc bfc′ : SN.BFcPos)
                (l₀ : Link) (d₀ : Dir) (m : ApiCSTag) (v : ApiCSCar m)
              → CliApiRowP k kd bfc bfc′ (apiCS l₀ d₀ m) v → bfc ≡ bfc′
cliRowP-apiCS k kd bfc bfc′ l₀ d₀ m v h = h

-- *** (T11h) … AND THE REGION's OWN COMPLEMENT, AGAINST THE CONE's `PastAreq`. ***
-- The cone states "the relay landed at or past its down `reqBFRange` emit" as a
-- dispatch on `ProdPh` (`LiveLegApiCone.PastAreq`), because the cone cannot see this
-- module; this is the one line that spends it.  Both predicates are the SAME eleven-way
-- dispatch with opposite polarity, so every clause is closed by one absurd pattern
pastAreq-⊮ : (bb : Block₃) (qq : ProdPh)
           → PastAreq qq → RelayFreshBF (producing bb qq) → ⊥
pastAreq-⊮ bb pp0 () _
pastAreq-⊮ bb pp1 () _
pastAreq-⊮ bb pp2 () _
pastAreq-⊮ bb pp3 () _
pastAreq-⊮ bb pp4 _ ()
pastAreq-⊮ bb pp5 _ ()
pastAreq-⊮ bb pp6 _ ()
pastAreq-⊮ bb pp7 _ ()
pastAreq-⊮ bb pp8 _ ()
pastAreq-⊮ bb pp9 _ ()

-- §0(5) THE FIRST HAZARD, as the table row that causes it: a client inside the
-- region is pushed BACK to `bcIdle` by a `MsgNoBlocks` read.  The client
-- conjunct is therefore NOT io-closed by itself and the cell conjunct is what
-- closes it (§2's `bfFresh-cliRead`, arm `crNB`)
crNB-row : CliReadAdj NS.bcBusy nbPayload NS.bcIdle
crNB-row = crNB

------------------------------------------------------------------------
-- §1  THE REGIONS, THE CORE, ITS BASE AND ITS FRAME.
--
-- `LiveDrvCSD` §4's five fields at the BlockFetch positions, with the PHASE
-- conjunct replaced by the JOINT `PhCli` §0(6) forced.  Stated on FOUR ABSTRACT
-- POSITIONS and no accessor, so §2 is pure table logic and the leg, the state
-- and the medium appear only in §2b's thin wrappers.
------------------------------------------------------------------------

-- the SERVER half: the leg's down BF server has not yet answered a request —
-- `bsIdle`'s only two rows are wire-reads (`NodeSpecs:588-599`) and the relay's
-- own api emit is the only way out of `bsAreq`
SrvFreshBF : NS.BFsPos → Set
SrvFreshBF NS.bsIdle      = ⊤
SrvFreshBF (NS.bsAreq r)  = ⊤
SrvFreshBF NS.bsBusy      = ⊥
SrvFreshBF NS.bsDdone     = ⊥
SrvFreshBF NS.bsWsb       = ⊥
SrvFreshBF NS.bsStream    = ⊥
SrvFreshBF NS.bsWnb       = ⊥
SrvFreshBF (NS.bsWblk b)  = ⊥
SrvFreshBF NS.bsWbd       = ⊥
SrvFreshBF NS.bsTerm      = ⊥

-- the CLIENT half: node D's down BF client has at most its range request
-- outstanding.  `bcStream`/`bcAblk`/`bcWcd`/`bcTerm` all need the relay's own
-- `sendBFStartBatch` (`pp4`) or node D's own client-done (`cp4`), i.e. they are
-- outside the guard or outside `PhCli`
CliFreshBF : NS.BFcPos → Set
CliFreshBF NS.bcIdle      = ⊤
CliFreshBF (NS.bcWrr r)   = ⊤
CliFreshBF NS.bcBusy      = ⊤
CliFreshBF NS.bcWcd       = ⊥
CliFreshBF NS.bcStream    = ⊥
CliFreshBF (NS.bcAblk b)  = ⊥
CliFreshBF NS.bcTerm      = ⊥

-- the `cp3` sub-region: node D has FIRED `sendBFRequestRange`, so its client is
-- past `bcIdle`.  §0(6)'s hazard is exactly that this cannot be stated as a
-- phase-only exclusion
CliPostBF : NS.BFcPos → Set
CliPostBF NS.bcIdle      = ⊥
CliPostBF (NS.bcWrr r)   = ⊤
CliPostBF NS.bcBusy      = ⊤
CliPostBF NS.bcWcd       = ⊥
CliPostBF NS.bcStream    = ⊥
CliPostBF (NS.bcAblk b)  = ⊥
CliPostBF NS.bcTerm      = ⊥

-- the PHASE half, JOINT with the client (§0(6)): node D has not passed the
-- block, and if it has passed the REQUEST its client says so.  The three `⊥`
-- clauses are what let this object supply `InCp03` instead of premising the
-- token
PhCli : ConsPh → NS.BFcPos → Set
PhCli cp0 q = ⊤
PhCli cp1 q = ⊤
PhCli cp2 q = ⊤
PhCli cp3 q = CliPostBF q
PhCli cp4 q = ⊥
PhCli cp5 q = ⊥
PhCli cp6 q = ⊥

-- the cell holds node D's unread `MsgRequestRange` — lenient in `(time , mode ,
-- length)` exactly as the readers' table rows are (`SrvReadAdj.srReq`), and
-- existential in the RANGE because the row is (`bfSnxt bsIdle`'s first row
-- accepts every range).  `LiveChanCS.FullMsg`'s BlockFetch analogue, narrowed
-- to the one message the way `ReqOnly` is
RngOnly : SM.CopyPhase → Set
RngOnly ph = Σ[ t ∈ Time ] Σ[ md ∈ Mode ] Σ[ ln ∈ Length ] Σ[ r ∈ ChainRange ]
               (ph ≡ SM.full (t , md , ln , blockFetch (MsgRequestRange r)))

-- the CELL half: the hop's cell holds nothing but, at most, that unread request.
-- The three arms are exactly the three §3's refutation dispatches on
CellFreshBF : SM.CopyPhase → Set
CellFreshBF ph = (ph ≡ SM.empty)
               ⊎ (Σ[ x ∈ Payload ] (ph ≡ SM.draining x))
               ⊎ RngOnly ph

-- an EMPTY cell holds no unread request …
rngOnly-empty-⊥ : RngOnly SM.empty → ⊥
rngOnly-empty-⊥ (_ , _ , _ , _ , ())

-- … and neither does a DRAINING one (the arm §2's drain class spends: at
-- `(bsIdle , draining x , bcBusy)` the correlation itself is contradictory)
rngOnly-draining-⊥ : (x : Payload) → RngOnly (SM.draining x) → ⊥
rngOnly-draining-⊥ x (_ , _ , _ , _ , ())

-- the cell node D's own request write leaves behind IS an `RngOnly` cell — the
-- one place the correlation is ESTABLISHED rather than spent
rngOnly-rr : (r : ChainRange) → RngOnly (SM.full (rrPayload r))
rngOnly-rr r = _ , _ , _ , r , refl

-- inside `CellFreshBF` a FULL cell holds the request and nothing else: the
-- `empty` and `draining` arms are constructor clashes.  The single fact all four
-- io READ classes spend
cellFreshBF-full : (y : Payload) → CellFreshBF (SM.full y) → RngOnly (SM.full y)
cellFreshBF-full y (inj₁ ())
cellFreshBF-full y (inj₂ (inj₁ (_ , ())))
cellFreshBF-full y (inj₂ (inj₂ rq)) = rq

-- … and `RngOnly` PINS the message, so any other BlockFetch message in the cell
-- is refuted.  One clause per row the read classes have to kill — five
-- one-liners rather than one message-generic lemma, because `MsgRequestRange`
-- CARRIES a range and a generic negation would have to quantify it
rngOnly-sb-⊥ : (t : Time) (md : Mode) (ln : Length)
             → RngOnly (SM.full (t , md , ln , blockFetch MsgStartBatch)) → ⊥
rngOnly-sb-⊥ t md ln (_ , _ , _ , _ , ())

rngOnly-nb-⊥ : (t : Time) (md : Mode) (ln : Length)
             → RngOnly (SM.full (t , md , ln , blockFetch MsgNoBlocks)) → ⊥
rngOnly-nb-⊥ t md ln (_ , _ , _ , _ , ())

rngOnly-blk-⊥ : (t : Time) (md : Mode) (ln : Length) (b : Block₃)
              → RngOnly (SM.full (t , md , ln , blockFetch (MsgBlock b))) → ⊥
rngOnly-blk-⊥ t md ln b (_ , _ , _ , _ , ())

rngOnly-bd-⊥ : (t : Time) (md : Mode) (ln : Length)
             → RngOnly (SM.full (t , md , ln , blockFetch MsgBatchDone)) → ⊥
rngOnly-bd-⊥ t md ln (_ , _ , _ , _ , ())

rngOnly-cd-⊥ : (t : Time) (md : Mode) (ln : Length)
             → RngOnly (SM.full (t , md , ln , blockFetch MsgClientDone)) → ⊥
rngOnly-cd-⊥ t md ln (_ , _ , _ , _ , ())

-- *** THE FRESHNESS CLAUSE's CORE, on four abstract positions. ***  The fifth
-- field is the CORRELATION the four conjuncts cannot express: a client that has
-- written its request and a server still at `bsIdle` means the request is UNREAD
-- in the cell.  It is what closes the `(bsIdle , empty , bcBusy)` sub-case, and
-- `LiveDrvCSD.DnFreshC.dfArr` is its exact relative
record BFFreshC (sa : NS.BFsPos) (ph : SM.CopyPhase) (ca : NS.BFcPos)
                (x : ConsPh) : Set where
  constructor mkBFFreshC
  field
    bfSrv  : SrvFreshBF sa
    bfCli  : CliFreshBF ca
    bfCell : CellFreshBF ph
    bfPh   : PhCli x ca
    bfArr  : sa ≡ NS.bsIdle → ca ≡ NS.bcBusy → RngOnly ph
open BFFreshC public

-- *** THE CARRIED FORM — the core at the leg's four slots, GUARDED on the
-- relay's phase (§0). ***
BFFresh : TwoLegs → SysState → Set
BFFresh l s = RelayFreshBF (relayOf l s)
            → BFFreshC (coarsenBFs (dnSrv l s)) (cellDn l s)
                       (coarsenBFc (dnClient l s)) (phOf l s)

-- BASE — at `initial` every component is at its head: the server `bsIdle`, the
-- client `bcIdle`, the cell `empty`, node D's phase `cp0`; the `cp0` clause of
-- `PhCli` is `⊤` and the correlation is vacuous (`bcIdle ≢ bcBusy`)
bfFresh-init : (l : TwoLegs) → BFFresh l initial
bfFresh-init legBD _ = mkBFFreshC tt tt (inj₁ refl) tt (λ _ ())
bfFresh-init legCD _ = mkBFFreshC tt tt (inj₁ refl) tt (λ _ ())

-- transport the core along equalities of its four components — what every frame
-- and every fixity hypothesis hands over
bfFreshC-cong : (sa sa′ : NS.BFsPos) (ph ph′ : SM.CopyPhase)
                (ca ca′ : NS.BFcPos) (x x′ : ConsPh)
              → sa ≡ sa′ → ph ≡ ph′ → ca ≡ ca′ → x ≡ x′
              → BFFreshC sa ph ca x → BFFreshC sa′ ph′ ca′ x′
bfFreshC-cong sa _ ph _ ca _ x _ refl refl refl refl fr = fr

-- *** THE LIFT. ***  Every class but the relay's own advance fixes the relay's
-- phase, so the guard transports BACKWARDS along the step and the guarded
-- object's preservation is exactly the core's
bfFresh-lift : (l : TwoLegs) (s s′ : SysState)
             → relayOf l s ≡ relayOf l s′
             → (BFFreshC (coarsenBFs (dnSrv l s)) (cellDn l s)
                         (coarsenBFc (dnClient l s)) (phOf l s)
                → BFFreshC (coarsenBFs (dnSrv l s′)) (cellDn l s′)
                           (coarsenBFc (dnClient l s′)) (phOf l s′))
             → BFFresh l s → BFFresh l s′
bfFresh-lift l s s′ peq step fr g′ = step (fr (subst RelayFreshBF (sym peq) g′))

-- FRAME — the four components fixed (the other leg, the other node, every inert
-- peer, every `break`, and every medium τ on another channel)
bfFresh-frame : (l : TwoLegs) (s s′ : SysState)
              → relayOf l s ≡ relayOf l s′
              → dnSrv l s ≡ dnSrv l s′
              → cellDn l s ≡ cellDn l s′
              → dnClient l s ≡ dnClient l s′
              → phOf l s ≡ phOf l s′
              → BFFresh l s → BFFresh l s′
bfFresh-frame l s s′ peq seq heq keq deq =
  bfFresh-lift l s s′ peq
    (bfFreshC-cong _ _ _ _ _ _ _ _ (cong coarsenBFs seq) heq
                   (cong coarsenBFc keq) deq)

------------------------------------------------------------------------
-- §2  THE STEP CLASSES — one per class, on the abstract positions.
--
-- `LiveDrvCSD` §5's six classes plus the relay's two, and NODE D's joint
-- BlockFetch adjacency, which is `CliDrvAdj`'s BlockFetch twin: a BF peer's api
-- row and its driver's phase advance are two halves of ONE step (`apiBF … ∈
-- apiES`), so the object indexes them TOGETHER.
--
-- *** WHAT THE JOINT DATATYPE CLAIMS, AND WHERE IT IS CHECKED. ***  Being a
-- hypothesis-position object it is safe if too WIDE and vacuous if too NARROW.
-- Its six rows are the PAIRING of `bfCnxt`'s three api rows (`NodeSpecs:518-556`
-- — `sendBFRequestRange` at `bcIdle`, `sendBFClientDone` at `bcIdle`,
-- `recvBFBlock` at `bcAblk b`) with `WalkMeasure.ConsAdv`'s six driver hops,
-- read off `consume`/`consume-k`'s event order (`FourNodeDiamond:224-241`):
-- `cp0` fires `sendCSRequestNext`, `cp1` `recvCSRollforward`, `cp2`
-- `sendBFRequestRange`, `cp3` `recvBFBlock`, `cp4` `sendBFClientDone`, `cp5`
-- `sendCSDone`.  The three ChainSync hops move the driver with the BF client
-- FIXED, which is why they are position-generic.
--
-- *** KEEP IN SYNC — `LiveChanInv`'s `CliApiRow` (the client's api rows) ×
-- `WalkMeasure.ConsAdv` (the driver's six hops).  This datatype is the PAIRING
-- of those two tables and it is a TRANSCRIPTION, not a derivation: if either
-- table gains a row, this one must be re-derived. ***  `LiveDrvCSD` §5's C-1 is
-- what a mis-transcription of the sibling table costs.
------------------------------------------------------------------------

data BFCliDrvAdj : NS.BFcPos → ConsPh → NS.BFcPos → ConsPh → Set where
  dbReq   : (r : ChainRange)
          → BFCliDrvAdj NS.bcIdle cp2 (NS.bcWrr r) cp3      -- sendBFRequestRange
  -- *** (T11e) WIDENED in its TARGET, for `db45`'s reason and with the same saving. ***
  -- Its consumer refutes it by the SOURCE (`CliFreshBF (bcAblk b) = ⊥`) and never
  -- reads the successor, so naming `bcStream` bought nothing and cost §2c the
  -- `recvBFBlock` LANDING as an input — which would have had to be threaded from the
  -- bundle through node D's record to the leg.  Hypothesis-position, safe if wide.
  dbRecv  : (b : Block₃) (q′ : NS.BFcPos)
          → BFCliDrvAdj (NS.bcAblk b) cp3 q′ cp4              -- recvBFBlock
  -- *** (T11d) WIDENED from `BFCliDrvAdj bcIdle cp4 bcWcd cp5` to a PHASE-ONLY row,
  -- and the widening is a saving of ≈90 lines. ***  Its consumer closes it by the
  -- SOURCE PHASE alone (`PhCli cp4 = ⊥`), never by either client position — so
  -- naming the endpoints bought nothing and cost a whole `sendBFClientDone` landing
  -- family (a label pin, a landed form, two producers and a bundle Σ component) at
  -- §2c's producer.  *** This datatype is HYPOTHESIS-POSITION: safe if too WIDE and
  -- vacuous if too NARROW (see the header), so a widening whose consumer still closes
  -- is free. ***
  db45    : (q q′ : NS.BFcPos) → BFCliDrvAdj q cp4 q′ cp5    -- sendBFClientDone
  dbCS01  : (q : NS.BFcPos) → BFCliDrvAdj q cp0 q cp1       -- sendCSRequestNext
  dbCS12  : (q : NS.BFcPos) → BFCliDrvAdj q cp1 q cp2       -- recvCSRollforward
  dbCS56  : (q : NS.BFcPos) → BFCliDrvAdj q cp5 q cp6       -- sendCSDone

-- (1) *** NODE D's api CLASS. ***  The relay's server and the hop's cell are
-- fixed.  THREE rows survive and each is closed by one field: `dbReq` lands the
-- client at `bcWrr r`, inside both the client region and `PhCli cp3`; the two
-- ChainSync hops keep the client and land at a `⊤` phase clause.  `dbRecv` is
-- refuted by the CLIENT conjunct (its source `bcAblk b` is outside) and
-- `dbDone`/`dbCS56` by the PHASE conjunct (their sources are `cp4`/`cp5`) — the
-- two faces of §0(6)'s hazard
bfFresh-cliApi : (sa : NS.BFsPos) (ph : SM.CopyPhase) (ca ca′ : NS.BFcPos)
                 (x x′ : ConsPh)
               → BFCliDrvAdj ca x ca′ x′
               → BFFreshC sa ph ca x → BFFreshC sa ph ca′ x′
bfFresh-cliApi sa ph _ _ _ _ (dbReq _)  fr =
  mkBFFreshC (bfSrv fr) tt (bfCell fr) tt (λ _ ())
bfFresh-cliApi sa ph _ _ _ _ (dbRecv _ _) fr = ⊥-elim (bfCli fr)
bfFresh-cliApi sa ph _ _ _ _ (db45 _ _) fr = ⊥-elim (bfPh fr)
bfFresh-cliApi sa ph _ _ _ _ (dbCS01 _) fr =
  mkBFFreshC (bfSrv fr) (bfCli fr) (bfCell fr) tt (bfArr fr)
bfFresh-cliApi sa ph _ _ _ _ (dbCS12 _) fr =
  mkBFFreshC (bfSrv fr) (bfCli fr) (bfCell fr) tt (bfArr fr)
bfFresh-cliApi sa ph _ _ _ _ (dbCS56 _) fr = ⊥-elim (bfPh fr)

-- (2) THE io FILL BY THE SERVER — the cell goes `empty → full y`.  All four
-- wire-send rows start OUTSIDE `SrvFreshBF` (`bsWsb`/`bsWnb`/`bsWblk`/`bsWbd`),
-- so the class is refuted by the server conjunct alone, one body four times
bfFresh-srvSend : (sa sa′ : NS.BFsPos) (y : Payload) (ca : NS.BFcPos) (x : ConsPh)
                → SrvSendAdj sa y sa′
                → BFFreshC sa SM.empty ca x → BFFreshC sa′ (SM.full y) ca x
bfFresh-srvSend _ _ _ ca x ssSB      fr = ⊥-elim (bfSrv fr)
bfFresh-srvSend _ _ _ ca x ssNB      fr = ⊥-elim (bfSrv fr)
bfFresh-srvSend _ _ _ ca x (ssBlk _) fr = ⊥-elim (bfSrv fr)
bfFresh-srvSend _ _ _ ca x ssBD      fr = ⊥-elim (bfSrv fr)

-- the client half of `PhCli` under its own advance: `bcWrr r` and `bcBusy` are
-- both inside `CliPostBF`, so the request's WIRE-SEND keeps the phase clause.
-- A named dispatch and not a `subst`, because the clause is a REGION at `cp3`
-- and an equality nowhere
phCli-wrr⇒busy : (x : ConsPh) (r : ChainRange)
               → PhCli x (NS.bcWrr r) → PhCli x NS.bcBusy
phCli-wrr⇒busy cp0 r _ = tt
phCli-wrr⇒busy cp1 r _ = tt
phCli-wrr⇒busy cp2 r _ = tt
phCli-wrr⇒busy cp3 r _ = tt
phCli-wrr⇒busy cp4 r ()
phCli-wrr⇒busy cp5 r ()
phCli-wrr⇒busy cp6 r ()

-- (3) *** THE io FILL BY THE CLIENT — the ONE step that ESTABLISHES the
-- correlation. ***  Its request row takes `(bcWrr r , empty)` to `(bcBusy , full
-- (rrPayload r))`, which is both the narrowed cell arm and the correlation's
-- conclusion; its other row starts outside `CliFreshBF`
bfFresh-cliSend : (sa : NS.BFsPos) (y : Payload) (ca ca′ : NS.BFcPos) (x : ConsPh)
                → CliSendAdj ca y ca′
                → BFFreshC sa SM.empty ca x → BFFreshC sa (SM.full y) ca′ x
bfFresh-cliSend sa _ _ _ x (csReq r) fr =
  mkBFFreshC (bfSrv fr) tt (inj₂ (inj₂ (rngOnly-rr r)))
             (phCli-wrr⇒busy x r (bfPh fr)) (λ _ _ → rngOnly-rr r)
bfFresh-cliSend sa _ _ _ x csCD      fr = ⊥-elim (bfCli fr)

-- (4) *** THE SERVER's WIRE-READ — the step the arm's own equation names. ***
-- The cell is `full`, so `cellFreshBF-full` pins its message to
-- `MsgRequestRange`: the `MsgClientDone` row is refuted by that pin (and it is
-- the row that would take the server OUT of the region, to `bsDdone`), and the
-- request row lands at `bsAreq r`, inside `SrvFreshBF`, with the cell `draining`
-- and the correlation vacuous
bfFresh-srvRead : (sa sa′ : NS.BFsPos) (y : Payload) (ca : NS.BFcPos) (x : ConsPh)
                → SrvReadAdj sa y sa′
                → BFFreshC sa (SM.full y) ca x → BFFreshC sa′ (SM.draining y) ca x
bfFresh-srvRead _ _ _ ca x (srReq _) fr =
  -- the correlation is vacuous at `bsAreq`, so ONE absurd argument closes it (an
  -- absurd pattern has to be the LAST in an extended λ — `λ () _` is a parse error)
  mkBFFreshC tt (bfCli fr) (inj₂ (inj₁ (_ , refl))) (bfPh fr) (λ ())
bfFresh-srvRead _ _ _ ca x srCD      fr =
  ⊥-elim (rngOnly-cd-⊥ _ _ _ (cellFreshBF-full _ (bfCell fr)))

-- (5) THE CLIENT's WIRE-READ — all four rows refuted.  The two from `bcBusy`
-- carry RESPONDER messages, which the cell pin excludes — *** and `crNB` is
-- §0(5)'s hazard, closed HERE and only here *** — and the two from `bcStream`
-- start outside `CliFreshBF`
bfFresh-cliRead : (sa : NS.BFsPos) (y : Payload) (ca ca′ : NS.BFcPos) (x : ConsPh)
                → CliReadAdj ca y ca′
                → BFFreshC sa (SM.full y) ca x → BFFreshC sa (SM.draining y) ca′ x
bfFresh-cliRead sa _ _ _ x crSB      fr =
  ⊥-elim (rngOnly-sb-⊥ _ _ _ (cellFreshBF-full _ (bfCell fr)))
bfFresh-cliRead sa _ _ _ x crNB      fr =
  ⊥-elim (rngOnly-nb-⊥ _ _ _ (cellFreshBF-full _ (bfCell fr)))
bfFresh-cliRead sa _ _ _ x (crBlk _) fr = ⊥-elim (bfCli fr)
bfFresh-cliRead sa _ _ _ x crBD      fr = ⊥-elim (bfCli fr)

-- (6) *** THE MEDIUM's OWN DRAIN τ — and the one class where the correlation is
-- spent on its OWN source state. ***  `draining y → empty` keeps every position,
-- and the successor's correlation would need `RngOnly empty`; the SOURCE's
-- correlation already says `RngOnly (draining y)`, which is false, so `(bsIdle ,
-- draining y , bcBusy)` is refuted by the object it is carried in rather than by
-- a move
bfFresh-drain : (sa : NS.BFsPos) (y : Payload) (ca : NS.BFcPos) (x : ConsPh)
              → BFFreshC sa (SM.draining y) ca x → BFFreshC sa SM.empty ca x
bfFresh-drain sa y ca x fr =
  mkBFFreshC (bfSrv fr) (bfCli fr) (inj₁ refl) (bfPh fr)
             (λ hs hc → ⊥-elim (rngOnly-draining-⊥ y (bfArr fr hs hc)))

------------------------------------------------------------------------
-- §2b  THE STATE-LEVEL WRAPPERS, and the relay's two classes.
------------------------------------------------------------------------

-- (a) *** THE RELAY ADVANCED INSIDE THE REGION — §0(4)'s four advances plus its
-- own six consume hops. ***  Our four components are fixed at all ten (the
-- consuming hops fire on the leg's UP link; the four in-region producing hops
-- fire `apiCS` events, whose BF row facts ARE the fixities by §0(4)), and the
-- guard is available at the SOURCE by hypothesis, so nothing is transported
-- backwards.  `LDC.dnFresh-relayCons` with the source's guard passed in rather
-- than computed from a `consuming` witness — §0(3)'s dispatch hands exactly this
bfFresh-relayIn : (l : TwoLegs) (s s′ : SysState)
                → RelayFreshBF (relayOf l s)
                → dnSrv l s ≡ dnSrv l s′
                → cellDn l s ≡ cellDn l s′
                → dnClient l s ≡ dnClient l s′
                → phOf l s ≡ phOf l s′
                → BFFresh l s → BFFresh l s′
bfFresh-relayIn l s s′ g seq heq keq deq fr _ =
  bfFreshC-cong _ _ _ _ _ _ _ _ (cong coarsenBFs seq) heq
                (cong coarsenBFc keq) deq (fr g)

-- (b) … and the relay advanced OUT of the region — its `reqBFRange` emit and
-- every produce hop after it.  The obligation is vacuous, so the class demands
-- nothing else: the components may move freely.  *** THIS IS THE PHASE GUARD
-- DOING ITS ENTIRE JOB *** — the `bsAreq → bsBusy` exit no sibling conjunct
-- reaches (§0(2))
bfFresh-relayOut : (l : TwoLegs) (s s′ : SysState)
                 → (RelayFreshBF (relayOf l s′) → ⊥)
                 → BFFresh l s → BFFresh l s′
bfFresh-relayOut l s s′ no fr g′ = ⊥-elim (no g′)

-- *** (T11g) … and the SAME in-region advance when node D MOVED in the same sync. ***
-- `BFFreshC` has NO relay-phase index at all (four components, not five), so the two
-- moves compose trivially: the guard is taken at the SOURCE, the server and the cell
-- ride their equations, and node D's own class moves the client and the phase.
-- `LiveDrvCSD.dnFresh-relayConsApi`'s shape on this axis.  (The combination is in fact
-- unreachable — one `apiES` sync is one driver advance and the relay's labels are
-- disjoint from node D's six — but refuting it needs the LABEL, which the carry's arm
-- does not hold, so it is CARRIED instead: §8 (i-b)'s trap, paid rather than argued.)
bfFresh-relayInApi : (l : TwoLegs) (s s′ : SysState)
                   → RelayFreshBF (relayOf l s)
                   → dnSrv l s ≡ dnSrv l s′
                   → cellDn l s ≡ cellDn l s′
                   → BFCliDrvAdj (coarsenBFc (dnClient l s)) (phOf l s)
                                 (coarsenBFc (dnClient l s′)) (phOf l s′)
                   → BFFresh l s → BFFresh l s′
bfFresh-relayInApi l s s′ g seq heq adj fr _ =
  bfFresh-cliApi _ _ _ _ _ _ adj
    (bfFreshC-cong _ _ _ _ _ _ _ _ (cong coarsenBFs seq) heq refl refl (fr g))

-- NODE D's api SYNC, at the state's slots
bfFresh-nodeDApi : (l : TwoLegs) (s s′ : SysState)
                 → relayOf l s ≡ relayOf l s′
                 → dnSrv l s ≡ dnSrv l s′
                 → cellDn l s ≡ cellDn l s′
                 → BFCliDrvAdj (coarsenBFc (dnClient l s)) (phOf l s)
                               (coarsenBFc (dnClient l s′)) (phOf l s′)
                 → BFFresh l s → BFFresh l s′
bfFresh-nodeDApi l s s′ peq seq heq adj =
  bfFresh-lift l s s′ peq
    (λ fr → bfFresh-cliApi _ _ _ _ _ _ adj
              (bfFreshC-cong _ _ _ _ _ _ _ _ (cong coarsenBFs seq) heq
                             refl refl fr))

-- the SERVER's io FILL, at the state's slots (the cell's two phases come from
-- the medium's banked key lemmas)
bfFresh-srvSendS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
                 → relayOf l s ≡ relayOf l s′
                 → cellDn l s ≡ SM.empty → cellDn l s′ ≡ SM.full y
                 → dnClient l s ≡ dnClient l s′ → phOf l s ≡ phOf l s′
                 → SrvSendAdj (coarsenBFs (dnSrv l s)) y (coarsenBFs (dnSrv l s′))
                 → BFFresh l s → BFFresh l s′
bfFresh-srvSendS l s s′ y peq he he′ keq deq adj =
  bfFresh-lift l s s′ peq
    (λ fr → bfFreshC-cong _ _ _ _ _ _ _ _ refl (sym he′) (cong coarsenBFc keq) deq
              (bfFresh-srvSend _ _ y (coarsenBFc (dnClient l s)) (phOf l s) adj
                (bfFreshC-cong _ _ _ _ _ _ _ _ refl he refl refl fr)))

-- … the CLIENT's io FILL
bfFresh-cliSendS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
                 → relayOf l s ≡ relayOf l s′
                 → cellDn l s ≡ SM.empty → cellDn l s′ ≡ SM.full y
                 → dnSrv l s ≡ dnSrv l s′ → phOf l s ≡ phOf l s′
                 → CliSendAdj (coarsenBFc (dnClient l s)) y
                              (coarsenBFc (dnClient l s′))
                 → BFFresh l s → BFFresh l s′
bfFresh-cliSendS l s s′ y peq he he′ seq deq adj =
  bfFresh-lift l s s′ peq
    (λ fr → bfFreshC-cong _ _ _ _ _ _ _ _ (cong coarsenBFs seq) (sym he′)
                          refl deq
              (bfFresh-cliSend _ y (coarsenBFc (dnClient l s))
                (coarsenBFc (dnClient l s′)) (phOf l s) adj
                (bfFreshC-cong _ _ _ _ _ _ _ _ refl he refl refl fr)))

-- … the SERVER's io READ
bfFresh-srvReadS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
                 → relayOf l s ≡ relayOf l s′
                 → cellDn l s ≡ SM.full y → cellDn l s′ ≡ SM.draining y
                 → dnClient l s ≡ dnClient l s′ → phOf l s ≡ phOf l s′
                 → SrvReadAdj (coarsenBFs (dnSrv l s)) y (coarsenBFs (dnSrv l s′))
                 → BFFresh l s → BFFresh l s′
bfFresh-srvReadS l s s′ y peq hf he′ keq deq adj =
  bfFresh-lift l s s′ peq
    (λ fr → bfFreshC-cong _ _ _ _ _ _ _ _ refl (sym he′) (cong coarsenBFc keq) deq
              (bfFresh-srvRead _ _ y (coarsenBFc (dnClient l s)) (phOf l s) adj
                (bfFreshC-cong _ _ _ _ _ _ _ _ refl hf refl refl fr)))

-- … the CLIENT's io READ
bfFresh-cliReadS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
                 → relayOf l s ≡ relayOf l s′
                 → cellDn l s ≡ SM.full y → cellDn l s′ ≡ SM.draining y
                 → dnSrv l s ≡ dnSrv l s′ → phOf l s ≡ phOf l s′
                 → CliReadAdj (coarsenBFc (dnClient l s)) y
                              (coarsenBFc (dnClient l s′))
                 → BFFresh l s → BFFresh l s′
bfFresh-cliReadS l s s′ y peq hf he′ seq deq adj =
  bfFresh-lift l s s′ peq
    (λ fr → bfFreshC-cong _ _ _ _ _ _ _ _ (cong coarsenBFs seq) (sym he′)
                          refl deq
              (bfFresh-cliRead _ y (coarsenBFc (dnClient l s))
                (coarsenBFc (dnClient l s′)) (phOf l s) adj
                (bfFreshC-cong _ _ _ _ _ _ _ _ refl hf refl refl fr)))

-- … and the medium's DRAIN τ
bfFresh-drainS : (l : TwoLegs) (s s′ : SysState) (y : Payload)
               → relayOf l s ≡ relayOf l s′
               → cellDn l s ≡ SM.draining y → cellDn l s′ ≡ SM.empty
               → dnSrv l s ≡ dnSrv l s′
               → dnClient l s ≡ dnClient l s′ → phOf l s ≡ phOf l s′
               → BFFresh l s → BFFresh l s′
bfFresh-drainS l s s′ y peq hd he′ seq keq deq =
  bfFresh-lift l s s′ peq
    (λ fr → bfFreshC-cong _ _ _ _ _ _ _ _ (cong coarsenBFs seq) (sym he′)
                          (cong coarsenBFc keq) deq
              (bfFresh-drain _ y (coarsenBFc (dnClient l s)) (phOf l s)
                (bfFreshC-cong _ _ _ _ _ _ _ _ refl hd refl refl fr)))

------------------------------------------------------------------------
-- §3  *** THE ARM's EQUATION, FROM THE FRESHNESS CLAUSE AND THE CALLER's
-- STABILITY REFUTATIONS. ***
--
-- `LiveDrvCSD.dnFresh⇒areq`'s shape, `RState`-free for its reason (so that
-- `LiveRelayCS` §3 can call it at a `SysState`), with SIX `⊥`-premises instead
-- of four.  The dispatch is: refute `bsIdle`, and refuting it splits on the
-- CELL (three arms) and then, at the empty cell, on the CLIENT (three arms) and
-- then, at `bcIdle`, on NODE D's PHASE (three arms — `PhCli` gives `InCp03`
-- itself, §0(6)).
--
-- WHERE THE SIX PREMISES COME FROM, and what each costs (the honest inventory):
--
--   (1) `draining` — the MEDIUM's own solo τ on the down BF cell.  The kit is
--       `LiveIoIntro.medDrainτ` and its leg-level wrapper; `LiveSrvOpen`'s
--       `cellDrainCS-⊥` is the ChainSync one.
--   (2) `RngOnly` — the SERVER's own wire READ.  A NEW BlockFetch io ladder at
--       the READER's polarity: the built BF pair is the server WRITING
--       (`LiveIoIntro.srvInNodes-B-BD`) and node D's client READING
--       (`cliOutNodes-D-BD`), so this is one of the two directions that do not
--       exist on this axis.
--   (3) `empty` + the client at `bcWrr r` — node D's client's own wire WRITE.
--       The OTHER missing BlockFetch direction.
--   (4) `bcIdle` + node D at `cp2` — the api SYNC, the cheap one: `bfCnxt
--       bcIdle (apiBF … sendBFRequestRange) r ≡ just (bcWrr r)` at EVERY range
--       (`NodeSpecs:518-521`) and `consume-k` offers the label at `cp2`.
--   (5) `bcIdle` + node D at `cp0` — ALREADY A THEOREM off the carried and
--       UNGUARDED `LiveDrvCSD.DrvCliD` plus `cliIdle-cp0-⊥`: at `cp0` node D's
--       CS client is pinned to `ccIdle` and its own `sendCSRequestNext` sync is
--       enabled.  Zero cost, and it is ChainSync-axis.
--   (6) `bcIdle` + node D at `cp1` — *** THE LEAF, and the whole risk of the
--       arm. ***  Every component of the down BF hop is move-free there
--       (T9/`LiveRelayCS` §5b), so the refutation must come off the ChainSync
--       axis at a relay phase where the CS freshness object is vacuous: the
--       relay's own dn CS server region at `pp3`, a payload correlation, the
--       client-READ io ladder and the `ccArb` exclusion.  Stated here as a
--       premise so that the object, its calculus and the arm's route are
--       machine-checked WITHOUT it — the (T10) parked-interface pattern.
------------------------------------------------------------------------

-- THE SERVER-SIDE SHARPENING: inside the fresh region, refuting `bsIdle` leaves
-- `bsAreq rg`.  Argument-EXPLICIT and total on `BFsPos`, so the eight excluded
-- positions are refuted by the region and the ninth by its premise
srvFreshBF⇒areq : (q : NS.BFsPos) → SrvFreshBF q → (q ≡ NS.bsIdle → ⊥)
                → Σ[ rg ∈ ChainRange ] (q ≡ NS.bsAreq rg)
srvFreshBF⇒areq NS.bsIdle      _  no = ⊥-elim (no refl)
srvFreshBF⇒areq (NS.bsAreq r)  _  _  = r , refl
srvFreshBF⇒areq NS.bsBusy      () _
srvFreshBF⇒areq NS.bsDdone     () _
srvFreshBF⇒areq NS.bsWsb       () _
srvFreshBF⇒areq NS.bsStream    () _
srvFreshBF⇒areq NS.bsWnb       () _
srvFreshBF⇒areq (NS.bsWblk b)  () _
srvFreshBF⇒areq NS.bsWbd       () _
srvFreshBF⇒areq NS.bsTerm      () _

-- THE CLIENT-SIDE THREE-WAY: the fresh client region has exactly three members,
-- and the refutation needs them as an explicit disjunction to dispatch on
cliFreshBF-cases : (ca : NS.BFcPos) → CliFreshBF ca
                 → (ca ≡ NS.bcIdle)
                   ⊎ (Σ[ r ∈ ChainRange ] (ca ≡ NS.bcWrr r))
                   ⊎ (ca ≡ NS.bcBusy)
cliFreshBF-cases NS.bcIdle      _  = inj₁ refl
cliFreshBF-cases (NS.bcWrr r)   _  = inj₂ (inj₁ (r , refl))
cliFreshBF-cases NS.bcBusy      _  = inj₂ (inj₂ refl)
cliFreshBF-cases NS.bcWcd       ()
cliFreshBF-cases NS.bcStream    ()
cliFreshBF-cases (NS.bcAblk b)  ()
cliFreshBF-cases NS.bcTerm      ()

-- *** THE PHASE THREE-WAY, AND IT NEEDS NO TOKEN. ***  At a client sitting at
-- `bcIdle` the joint conjunct leaves exactly `{cp0, cp1, cp2}`: `cp3` is
-- excluded because `CliPostBF bcIdle` is `⊥` (§0(6)'s joint clause earning its
-- keep) and `cp4`/`cp5`/`cp6` by `PhCli`'s own `⊥` clauses.  `PipeInv`'s
-- `InCp03` would give only the weaker `{cp0 … cp3}` (`LiveRelayCS`'s
-- `token-⊮-pp3-cp1`), so this is a NARROWING the token cannot supply
phCli-idle-cases : (x : ConsPh) → PhCli x NS.bcIdle
                 → (x ≡ cp0) ⊎ (x ≡ cp1) ⊎ (x ≡ cp2)
phCli-idle-cases cp0 _  = inj₁ refl
phCli-idle-cases cp1 _  = inj₂ (inj₁ refl)
phCli-idle-cases cp2 _  = inj₂ (inj₂ refl)
phCli-idle-cases cp3 ()
phCli-idle-cases cp4 ()
phCli-idle-cases cp5 ()
phCli-idle-cases cp6 ()

-- *** THE ARM's EQUATION. ***  The six premises are the six sub-cases; all six
-- are `SysState`-level facts the CALLER proves, exactly as `dnFresh⇒areq`'s four
-- are
bfFresh⇒areq : (l : TwoLegs) (s : SysState)
             -- the GUARD: at the arm's own sub-phase it is `relayFreshBF-at`, so
             -- this argument is free at the point of use (§0(1))
             → RelayFreshBF (relayOf l s)
             → BFFresh l s
             -- (1) the medium's own drain τ
             → (Σ[ x ∈ Payload ] (cellDn l s ≡ SM.draining x) → ⊥)
             -- (2) the server's own wire READ of the request.  *** THE `bsIdle`
             -- ANTECEDENT IS PART OF THE PREMISE, and it has to be: *** the read
             -- row is `bsIdle → bsAreq r`, so the enabled move exists only while
             -- the server is still idle
             → (coarsenBFs (dnSrv l s) ≡ NS.bsIdle → RngOnly (cellDn l s) → ⊥)
             -- (3) node D's client's WRITE into the empty cell
             → (cellDn l s ≡ SM.empty
                → Σ[ r ∈ ChainRange ] (coarsenBFc (dnClient l s) ≡ NS.bcWrr r) → ⊥)
             -- (4) the api SYNC at `cp2`
             → (coarsenBFc (dnClient l s) ≡ NS.bcIdle → phOf l s ≡ cp2 → ⊥)
             -- (5) … and at `cp0`, which is already a theorem at the caller
             → (coarsenBFc (dnClient l s) ≡ NS.bcIdle → phOf l s ≡ cp0 → ⊥)
             -- (6) *** THE LEAF: `cp1`, off the ChainSync axis ***
             → (coarsenBFc (dnClient l s) ≡ NS.bcIdle → phOf l s ≡ cp1 → ⊥)
             → Σ[ rg ∈ ChainRange ] (coarsenBFs (dnSrv l s) ≡ NS.bsAreq rg)
bfFresh⇒areq l s gate fresh nodrain noread nowrite nosync2 nosync0 noleaf =
  srvFreshBF⇒areq (coarsenBFs (dnSrv l s)) (bfSrv fr) idle-⊥
  where
  fr = fresh gate
  -- the client's `bcIdle` arm, over node D's three surviving phases.  BOTH
  -- dispatches take their disjunction as an EXPLICIT argument rather than
  -- through a `with`, for `LiveRelayCS` §3's reason (a `with` here would
  -- abstract a type mentioning an imported `blkA`-parameterised predicate)
  idle-phases : coarsenBFc (dnClient l s) ≡ NS.bcIdle
              → (phOf l s ≡ cp0) ⊎ (phOf l s ≡ cp1) ⊎ (phOf l s ≡ cp2) → ⊥
  idle-phases hci (inj₁ h0)        = nosync0 hci h0
  idle-phases hci (inj₂ (inj₁ h1)) = noleaf  hci h1
  idle-phases hci (inj₂ (inj₂ h2)) = nosync2 hci h2
  -- the `empty` arm, over the client's three fresh positions
  empty-arms : cellDn l s ≡ SM.empty
             → coarsenBFs (dnSrv l s) ≡ NS.bsIdle
             → (coarsenBFc (dnClient l s) ≡ NS.bcIdle)
               ⊎ (Σ[ r ∈ ChainRange ] (coarsenBFc (dnClient l s) ≡ NS.bcWrr r))
               ⊎ (coarsenBFc (dnClient l s) ≡ NS.bcBusy)
             → ⊥
  empty-arms he hidl (inj₁ hci) =
    idle-phases hci
      (phCli-idle-cases (phOf l s) (subst (PhCli (phOf l s)) hci (bfPh fr)))
  empty-arms he hidl (inj₂ (inj₁ hcw)) = nowrite he hcw
  empty-arms he hidl (inj₂ (inj₂ hcb)) =
    rngOnly-empty-⊥ (subst RngOnly he (bfArr fr hidl hcb))
  -- … and the three-armed cell dispatch it sits inside
  idle-arms : coarsenBFs (dnSrv l s) ≡ NS.bsIdle → CellFreshBF (cellDn l s) → ⊥
  idle-arms hidl (inj₁ he) =
    empty-arms he hidl (cliFreshBF-cases (coarsenBFc (dnClient l s)) (bfCli fr))
  idle-arms hidl (inj₂ (inj₁ hdr)) = nodrain hdr
  idle-arms hidl (inj₂ (inj₂ hrq)) = noread hidl hrq
  idle-⊥ : coarsenBFs (dnSrv l s) ≡ NS.bsIdle → ⊥
  idle-⊥ hidl = idle-arms hidl (bfCell fr)

------------------------------------------------------------------------
-- §4  (T11) FALSIFICATIONS — TWO, one per novel family of this module (the
-- guarded core's CELL conjunct and its JOINT phase conjunct).  Both are
-- arity-preserving, both were RUN and RED at the predicted site, and both were
-- reverted by STRING INVERSION with `git diff` verified clean after each.
--
-- *** BOTH MUTATIONS TARGET A HAZARD §0's GUARD CHECK PREDICTED, WHICH IS THE
-- POINT: the check said the object's shape had to be this and the mutations are
-- the machine's confirmation. ***
--
-- (F93  *** THE CELL CONJUNCT IS WHAT CLOSES THE `MsgNoBlocks` READ — §0(5). ***)
--      `bfFresh-cliRead`'s `crNB` arm closed by the CLIENT conjunct
--      (`⊥-elim (bfCli fr)`) instead of by the cell pin — i.e. the reading under
--      which the client region would be io-closed on its own.
--      *** RED ***: `LiveDrvBFD.agda:582.51-59: [UnequalTerms] Level.Lift
--      Agda.Primitive.lzero Agda.Builtin.Unit.⊤ !=< ⊥ when checking that the
--      expression bfCli fr has type ⊥`, EXIT=42.  `CliFreshBF bcBusy` is `⊤`:
--      the source of the `MsgNoBlocks` read is INSIDE the client region, so
--      nothing but the cell conjunct excludes the step that would push the client
--      back to `bcIdle`.  Re-aiming note: this mutation dies if `CliFreshBF` ever
--      loses `bcBusy` — which it cannot, since `bcBusy` is where the client's own
--      request write lands.
--
-- (F94  *** `PhCli`'s `cp4` CLAUSE IS LOAD-BEARING — §0(6), third face. ***)
--      `bfFresh-cliApi`'s `dbDone` arm returns the FRAMED core instead of
--      `⊥-elim (bfPh fr)` — i.e. the reading under which node D's client-done hop
--      would be harmless inside the guard.
--      *** RED ***: `LiveDrvBFD.agda:514.26-34: [UnequalTerms] Level.Lift
--      Agda.Primitive.lzero Agda.Builtin.Unit.⊤ !=< ⊥ when checking that the
--      expression bfCli fr has type CliFreshBF NS.bcWcd`, EXIT=42.  *** THE ERROR
--      EXHIBITS THE SUCCESSOR POSITION *** — `bcWcd`, outside the client region —
--      which is exactly why the phase conjunct has to be `⊥` at `cp4` rather than
--      `⊤`.  Re-aiming note: this mutation dies if `CliFreshBF` is ever widened to
--      `bcWcd` (which would need the cell conjunct to admit a `MsgClientDone`, and
--      then the server's own `srCD` read leaves `SrvFreshBF` — the region would not
--      be io-closed inward, F88's rule).
--
-- *** THE GUARD LEDGER, HONESTLY. ***  F91 (`LiveRelayCS` §10) mutates `BFAt`'s
-- `pp3` clause and `pp3` is NOT discharged, so F91 STILL STANDS at a funded
-- target: this task does NOT owe the "no funded clause left to guard" statement
-- that a discharge on this axis would owe.  The CS half is unchanged (F92 at
-- `Sharp`'s `cp6`).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §2c  (T11d) *** `BFCliDrvAdj`'s PRODUCER, TOTAL ON NODE D's SIX HOPS — the object
-- §2 declared in hypothesis position now has one. ***  `LiveDrvCSD` §6c's twin one
-- protocol over, and the polarity is the MIRROR of it: there the three ChainSync
-- hops need the client to have MOVED and the three BlockFetch ones need it to have
-- STAYED; here it is the other way round.
--
-- *** WHAT EACH CLAUSE COSTS, and the map is worth more than the code — FIVE of the
-- six hops need NO bundle fact at all. ***
--
--   · `c01` / `c12` / `c56` fire `apiCS` labels, at which `CliApiRowP` reduces to
--     bare FIXITY (`LiveLegApiCone:1086-1090`'s catch-all): the label inversion alone
--     closes them and no pin is read.  This is §6c's own BlockFetch-hop argument at
--     the other protocol.
--   · `c45` needs NOTHING but the phase: since (T11d) its row is PHASE-ONLY (`db45`),
--     because its consumer closes it by `PhCli cp4 = ⊥` and never looks at either
--     client position.  *** That widening is what saved the `sendBFClientDone`
--     landing family. ***
--   · `c34` reads T10's `CliRecvLand` (§2b′⁶) plus the SOURCE the caller already
--     holds — node D's own `cp3` ANCHOR (`LiveLegApiExpose.NodeDApiEvo.ndaBD`'s sixth
--     field, built at T10 for a different consumer).  Nothing new was needed here.
--   · `c23` is THE ONE HOP THAT COSTS, and §2b⁷ is what it costs: `CliApiRowP`'s
--     FIXITY arm leaves the successor at `(cp3 , bcIdle)`, which §0(6) names as its
--     hazard and which only "node D's own client CO-FIRED" excludes.
--
-- *** THE `>> Skip` BIND IS CROSSED BY `bind-ev-inv`, and the head's own offer map by
-- ONE `Net_Api-≟` *** — §6c's idiom verbatim, six times.  Three of the six heads are
-- OUTPUTS (`cp2`, `cp4`, and `cp0`'s own first event is not) whose offer map has a
-- SECOND gate on the value; it is never reached, for §6c's reason.
--
-- *** THE TWO LANDINGS ARRIVE ALREADY-APPLIED at the caller's own key, which is why
-- this producer takes them rather than the raw rows: *** the bundle is the only thing
-- that knows which peer fired, and keeping the table reading at §2b⁷/§2b′⁶ keeps it
-- out of here.
--
-- (F106  *** AND SO IS `dbRecv`'s, at the OTHER end of the row. ***)  narrow its
--      TARGET back to `bcStream` — the shape it had before (T11e).
--      *** RED ***: `LiveDrvBFD.agda:1056.10-36: [UnequalTerms] NS.bcStream !=
--      coarsenBFc bfc′ of type NS.BFcPos … when checking that the inferred type of an
--      application BFCliDrvAdj (NS.bcAblk b″) cp3 NS.bcStream cp4 matches the expected
--      type BFCliDrvAdj (NS.bcAblk (anc .proj₁)) cp3 (coarsenBFc bfc′) cp4`, EXIT=42 —
--      at `c34`, which would then need the `recvBFBlock` LANDING as a fifth input,
--      threaded from the bundle through node D's record to the leg for a fact its
--      consumer never reads (it refutes the row by the SOURCE).  Reverted by string
--      inversion.  *** F104's lesson at the second row: read what the CONSUMER reads,
--      and index nothing else. ***
--
-- (F104  *** THE `db45` WIDENING IS LOAD-BEARING, and the RED is the price of not
-- doing it. ***)  narrow the row back to `BFCliDrvAdj bcIdle cp4 bcWcd cp5` — the
-- shape it had before (T11d) — and repair its one consumer clause to match.
--      *** RED ***: `LiveDrvBFD.agda:1050.3-7: [UnequalTerms] NS.bcIdle !=
--      coarsenBFc bfc of type NS.BFcPos … when checking that the expression db45 has
--      type BFCliDrvAdj (coarsenBFc bfc) cp4 (coarsenBFc bfc′) cp5`, EXIT=42 — at
--      `c45`, which has no way to NAME either endpoint: it would need a
--      `sendBFClientDone` label pin, a landed form, two bundle producers and a
--      twenty-fifth Σ component, i.e. §2b⁷'s whole family a second time.  *** So the
--      widening is what makes the clause free, and its consumer still closes it by
--      the source phase alone. ***  Reverted by string inversion, `git status` clean
--      after.
------------------------------------------------------------------------

bfCliDrvAdj-of : (l : Link) (b : Block₃) (x x′ : ConsPh) (bfc bfc′ : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l (consD b x) ─[ ev (evl (evLabel X e a)) ]─► M
  → ConsAdv x x′
  → CliApiRowP l hi bfc bfc′ e a
  → CliReqLand l hi bfc bfc′ e a
  -- node D's own `cp3` anchor, already coarsened.  *** (T11e) THE PIN IS GONE WITH
  -- `dbRecv`'s TARGET: *** the `c34` clause needs the SOURCE and nothing else
  → (x ≡ cp3 → Σ[ b″ ∈ Block₃ ] (coarsenBFc bfc ≡ NS.bcAblk b″))
  → BFCliDrvAdj (coarsenBFc bfc) x (coarsenBFc bfc′) x′
-- (1) `cp0 → cp1`: the head's first event is `apiCS l hi sendCSRequestNext`, at which
-- the BF client's api fact IS its fixity
bfCliDrvAdj-of l b _ _ bfc bfc′ {X} {e} {a} step c01 rowP _ _
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp0) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiCSCar sendCSRequestNext , apiCS l hi sendCSRequestNext) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → BFCliDrvAdj (coarsenBFc bfc) cp0 (coarsenBFc z) cp1) rowP
              (dbCS01 (coarsenBFc bfc))
-- (2) `cp1 → cp2`: the head is the INPUT prefix `apiCS l hi recvCSRollforward ⟶ …`
bfCliDrvAdj-of l b _ _ bfc bfc′ {X} {e} {a} step c12 rowP _ _
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp1) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiCSCar recvCSRollforward , apiCS l hi recvCSRollforward) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → BFCliDrvAdj (coarsenBFc bfc) cp1 (coarsenBFc z) cp2) rowP
              (dbCS12 (coarsenBFc bfc))
-- (3) *** `cp2 → cp3` — THE ONE HOP §2b⁷ EXISTS FOR. ***  The head is the OUTPUT
-- `apiBF l hi sendBFRequestRange ! (chainRange (point b) (point b)) ⟶ …`, so once the
-- key is pinned the landing applies at the FIRED range and names BOTH endpoints
bfCliDrvAdj-of l b _ _ bfc bfc′ {X} {e} {a} step c23 _ reqL _
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp2) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiBFCar sendBFRequestRange , apiBF l hi sendBFRequestRange) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → BFCliDrvAdj z cp2 (coarsenBFc bfc′) cp3) (sym (proj₁ edge))
          (subst (λ z → BFCliDrvAdj NS.bcIdle cp2 z cp3) (sym (proj₂ edge))
                 (dbReq a))
        where edge = reqL a refl
-- (4) `cp3 → cp4`: the head is the INPUT `apiBF l hi recvBFBlock ⟶ …`, and the
-- caller's anchor supplies the source the `bcAblk` row is indexed by
bfCliDrvAdj-of l b _ _ bfc bfc′ {X} {e} {a} step c34 _ _ anch =
  subst (λ z → BFCliDrvAdj z cp3 (coarsenBFc bfc′) cp4) (sym src)
        (dbRecv b″ (coarsenBFc bfc′))
  where anc = anch refl
        b″  = proj₁ anc
        src = proj₂ anc
-- (5) `cp4 → cp5`: the PHASE-ONLY row, so the head inversion is not even needed —
-- the adjacency is `db45` at whatever the two client positions are
bfCliDrvAdj-of l b _ _ bfc bfc′ step c45 _ _ _ =
  db45 (coarsenBFc bfc) (coarsenBFc bfc′)
-- (6) `cp5 → cp6`: the head is `apiCS l hi sendCSDone ⟶₀ Ret b`, an `apiCS` label
-- again, so the client's fixity closes it as at `c01`/`c12`
bfCliDrvAdj-of l b _ _ bfc bfc′ {X} {e} {a} step c56 rowP _ _
  with bind-ev-inv (λ _ → Skip) (decCons l hi b cp5) refl step
... | t , sVis refl br , refl
    with Net_Api-≟ {Payload}
           (ApiCSCar sendCSDone , apiCS l hi sendCSDone) (X , e)
...   | RN.no  _    = ⊥-elim (nothing-absurd br)
...   | RN.yes refl =
        subst (λ z → BFCliDrvAdj (coarsenBFc bfc) cp5 (coarsenBFc z) cp6) rowP
              (dbCS56 (coarsenBFc bfc))


------------------------------------------------------------------------
-- §3b  (T11e) *** WHAT STOPPED THE FOLD's LAST ARM — THE dn BF SERVER's FIXITY ON THE
-- FIVE IN-REGION ADVANCES, and it is §0(4)'s "interface argument" coming due. ***
--
-- Four of the fold's five arms were WRITTEN AND GREEN before this surfaced (the drain,
-- the `break`, and both io arms — the latter a faithful transcription of
-- `LiveChanJoin.HopArm.chanH-fill`/`-read`'s four peer shapes at the same hop, off the
-- same `setRead⁺` / `srvRow-off` / `srvSendRow` / `srvSend-cliSend-⊥` /
-- `fill-noPeer-⊥` converters).  The api arm is the one that does not close, and the
-- reason is precise:
--
--   `bfFresh-relayIn` (and `-frame`, and `-nodeDApi`) take `dnSrv l s ≡ dnSrv l s′` as
--   a HYPOTHESIS.  At the api class the cone supplies only `SrvApiRowP`, i.e. *fixity
--   ⊎ a genuine row* — and on the region's five in-region advances (`raCons`, `raCp6`,
--   `a01`, `a12`, `a23`) the row arm is UNREACHABLE but not REFUTABLE from the field
--   alone.  Refuting it needs the fired LABEL: at `a01`/`a12`/`a23` the label is an
--   `apiCS` one, where §0(4)'s machine-checked degeneration applies
--   (`srvRowP-apiCS`); at `raCons`/`raCp6` the hop fires on the leg's UP link, where a
--   down-server row is refuted BY LINK.
--
-- *** SO THE MISSING PIECE IS THE CLASSIFIER's PER-HOP LABEL PINS, THREADED TO THE LEG:
-- *** the twelfth (`CsrAt`, `pp1`), the thirteenth (`CsaAt`, `pp2`), (T11b)'s twentieth
-- (`CsfwAt`, `pp3`) and the nineteenth (the `ApiHasLink l₁ e` dichotomy) — plus one
-- refutation per arm.  Estimated 60-100 on top of the api arm's own ≈45.
--
-- *** AND THIS IS EXACTLY THE ONE THING THE T11 REVIEW FLAGGED AS UNVERIFIED. ***  Its
-- §0 payment-3 note says: "the four advances are FRAMES **given** those cone facts —
-- `bfFresh-relayIn` takes the four component fixities as HYPOTHESES.  What is
-- machine-checked in T11 is the degeneration; that the cone supplies it at those hops
-- is verified by READING `deRowsBD`'s TYPE, not by a build."  That reading is now the
-- fold's last obligation, and it is a THREADING and not a discovery: every pin exists
-- and every refutation is one line once the pin is in scope.
--
-- *** (T11g) THE REFUTATION's OWN MECHANISM, PRICED — and one HALF of it is free. ***
-- The `pp1`/`pp2`/`pp3` arms need "at this label the dn BF server's `SrvApiRowP` IS its
-- fixity".  `SrvApiRowP` is defined BY CASES ON THE LABEL (`LiveLegApiCone:1107-1112`):
-- `apiBF` and `done … N2N_BlockFetch` give the `⊎`, and EVERY OTHER FAMILY falls to a
-- catch-all that is the bare fixity.  So the reduction is free once the label's family
-- is a CONSTRUCTOR — and *** `ApiHasLink` is INDEXED BY THE LABEL ***
-- (`SysOracle:874-882`, `ahlCS : ApiHasLink l (apiCS l d m)`), so matching `ahlCS`
-- REFINES the event and the fixity falls out by pattern matching, in ONE clause.
--
-- *** WHAT IS NOT FREE is getting from the tag-specific pin to that constructor. ***
-- `CsrAt`/`CsaAt`/`CsfwAt` are `Maybe (Link × Dir)` EQUATIONS on their own decoders;
-- turning one into `ApiHasLink`'s constructor is exactly what `csrAt⇒ahl` /
-- `csaAt⇒ahl` / `csfwAt⇒ahl` already do — but they return `ApiHasLink`, which `ahlBF`
-- also inhabits, so they do not by themselves say the family is CS.  Each pin therefore
-- wants ONE more thirty-clause OUT map (to `CsAt`, or straight to the fixity), at
-- `csrAt⇒ahl`'s own price: *** ≈32 lines × 3 = ≈96. ***
--
-- *** SO THE FOLD's LAST SLICE IS ≈200, NOT ≈135: *** the three OUT maps ≈96 · the
-- `DnSrvPre` component and its four producer arms ≈60 · `bfFreshU-api` ≈55 · the factor
-- swap and its five call sites ≈30, less the overlap.  With slice 1's measured 163 that
-- puts the fold at ≈360-380 — inside a 400 STOP, above a 340 band.  *** The mechanism
-- is decided and nothing about it is uncertain; only its line count was. ***
--
-- *** (T11f) AND THE FINISH's ARITHMETIC, PRICED BEFORE IT IS OPENED — because the
-- re-creation is NOT free even though it is CERTAIN. ***  The four arms above were
-- green, so they carry no risk; but re-adding them is re-adding LINES, and a band that
-- treats them as already paid mis-prices the task.  Measured from what was written:
--
--   the factor swap (type · init · `mkU` · `drvBF-of` through `bfJoint⇒drv` ·
--     `bfJoint-of` · `bfFresh-of` · the five call sites)             ≈30
--   `bfSlots-drain` / `bfSlots-break`                                ≈16
--   `bfJointU-drain` (`chanH-drain`'s key dichotomy)                 ≈20
--   `bfJointU-break`                                                 ≈14
--   `bfFreshU-fill`  (`chanH-fill`'s four peer shapes)                ≈45
--   `bfFreshU-read`  (its mirror)                                    ≈45
--   `bfFresh-relayInApi` (this file)                                  ≈8
--   ────────────────────────────────────────────────────────────────────
--   re-creation, all of it CONFIRMED GREEN                          ≈178
--   `bfFreshU-api` itself                                            ≈55
--   the four pin threadings (§3b above)                            60-100
--   ────────────────────────────────────────────────────────────────────
--   THE FOLD's FINISH                                             ≈293-333
--
-- *** So the finish does not fit a 105-145 band or a 200 STOP: it wants ≈280-340 with
-- a STOP near 400. ***  Nothing here is uncertain — the estimate's only soft term is
-- the threading — but the arithmetic has to be quoted before the work opens, which is
-- the rule that has caught every one of this campaign's four re-costings.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §3  (T11e) *** THE CARRIED PAIR — `BFFresh` JOINS `LiveDrvBF.DrvBF` RATHER THAN
-- BECOMING A NEW `LegJointU` FACTOR. ***  It walks the SAME down-BlockFetch hop as
-- `DrvBF`, whose arms already take that hop's io row and the relay's phase fixity —
-- so folding costs ONE component at each of `LiveChanJoin`'s six `drvBF-*` sites,
-- where a trailing factor would have cost `DrvBF`'s whole arm set a second time
-- (T11d's measurement).  *** Appending a factor is cheap only when someone else
-- already walks its hop; here someone does. ***
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §3b  (B, cellCp3) *** THE DOWN FACTOR OF THE `cellCp3` WINDOW: NODE D's DOWN BF
-- CLIENT IS AT `bcIdle` THROUGHOUT ITS PRE-REQUEST REGION. ***
--
--     DnIdl l s = DnPre (phOf l s) → coarsenBFc (dnClient l s) ≡ NS.bcIdle
--
-- The mirror of `LiveDrvBFA` §5d at the other hop, and the second half of the window:
-- `LiveChanInv`'s `cvBlk`/`cvStr` give "an unread block in the DOWN cell ⇒ the reader
-- is inside the streaming region" (`CliStrA`) off `ChanDn` alone, `CliStrA bcIdle = ⊥`,
-- and so the two contradict at exactly the three sub-phases the window's antecedent
-- admits besides its conclusion — which is `cp3`.
--
-- *** THE GUARD, EVALUATED AT THE TARGET POSITIONS BEFORE ANYTHING WAS BUILT ON IT
-- (the standing law).  `DnPre` is `⊤` at `{cp0, cp1, cp2}` and `⊥` at `{cp3 … cp6}`.
-- The premise's own position is `AtPos l lpDnCell` (`LiveLegInv:440-441`), where the
-- consumer holds `InCp03 (phOf l s)` — `{cp0, cp1, cp2, cp3}`.  So the guard is
-- INHABITED at three of the four and the fourth IS the goal: nothing is preserved
-- vacuously. ***  Machine-checked with slice A's own union in the step-0 probe:
-- `DnPre ∪ ConsCp3 = InCp03` and `UpPre ∪ RelayCp3 = RelayPre`, both inclusions and
-- disjointness, all green.  *** KEEP IN SYNC: `DnPre` (here), `InCp03`
-- (`WalkPr:69-76`) and `ConsCp3` (`LiveLegInv:294-301`) are three dispatches over the
-- same seven `ConsPh` shapes, and the composition depends on that union. ***
--
-- *** AND WHY IT IS CHEAPER THAN THE UP HALF, WHICH IS THE MEASURED FINDING OF THIS
-- SLICE. ***  The up half's guard sits on the RELAY's phase, which the api cone reports
-- as a SEPARATE `RelayAdv` — hence `LiveLegApiCone.relayAdv-pre` (the region-entry
-- lemma) and the two `cons-c0*-cliFix` head inversions that sharpened `UpBfDrv`.  This
-- guard sits on NODE D's OWN phase, and `BFCliDrvAdj` (§2c, T11d) is indexed by node
-- D's SOURCE AND TARGET phase TOGETHER with the client's — so region entry and exit are
-- DEFINITIONAL in the datatype: four of its six rows are refuted by the TARGET and the
-- two that stay inside are the CS hops, which hold the client literally.  *** No
-- region-entry lemma, no cone component, no `LiveLegApiCone` edit at all. ***
--
-- *** ACCEPTANCE, MEASURED: the gate's `dnHalf` — `ChanDn l s → DnIdl l s → CellFull⁺ b
-- (cellDn l s) → InCp03 (phOf l s) → ConsCp3 (phOf l s)` — typechecks off this factor
-- and the carried channel invariant AND NOTHING ELSE, in 61 non-comment lines (32 of
-- them the import header; half one 9 off `cvBlk`+`cvStr`, the abstract-position
-- dispatch 11, the `MsgStartBatch` refutation 3).  Probed green FIRST TRY, `EXIT=0`,
-- warning-clean, then deleted; slice C lands it for real. ***
------------------------------------------------------------------------

-- *** THE GUARD: node D has not yet fired `sendBFRequestRange`. ***  Its exit is the
-- `cp2 → cp3` hop, which IS that fire (`db45`'s and `dbRecv`'s phases are further on)
--
-- (F112  *** THE GUARD'S EXTENT — `cp3` IS OUTSIDE IT, AND THE api CLASS IS WHERE THAT
--      IS SPENT. ***)  widen the region to `DnPre cp3 = ⊤`, which is what a reader who
--      reads the window's conclusion as "inside the pre region" would write.  *** RED
--      ***: `LiveDrvBFD.agda:1312.1-38: error: [ShouldBeEmpty] DnPre cp3 should be
--      empty, but that's not obvious to me … when checking the clause left hand side
--      dnIdlC-api _ _ _ _ (dbReq r) h ()`, EXIT=42 — at the `dbReq` ROW, i.e. at node
--      D's own `sendBFRequestRange`: a region containing `cp3` is not closed under the
--      very hop that leaves it.  The up hop's twin (F109) went red one lemma EARLIER,
--      at `relayAdv-pre`; here there is no region-entry lemma to fail first, because
--      `BFCliDrvAdj` carries both phases itself.  Reverted by string inversion.
DnPre : ConsPh → Set
DnPre cp0 = ⊤
DnPre cp1 = ⊤
DnPre cp2 = ⊤
DnPre cp3 = ⊥
DnPre cp4 = ⊥
DnPre cp5 = ⊥
DnPre cp6 = ⊥

-- `bcIdle` is the source of NO client wire row in EITHER direction (`LiveChanInv`'s
-- two client tables: the sends start at `bcWrr`/`bcWcd`, the reads at
-- `bcBusy`/`bcStream`), so BOTH io classes below are one-line refutations.  Stated
-- here rather than imported: `LiveDrvBFA.cliRead-idle-⊥` is the same one clause at the
-- up hop and the two modules do not import each other
--
-- (F113  *** IT IS `bcIdle` AND NOT MERELY "SOME PRE-STREAM POSITION" THAT BUYS THE
--      SEND CLASS — F111's finding at the OTHER io direction. ***)  restate the send
--      refutation at `bcWcd`, the OTHER position a client wire-send starts at and the
--      one a reader who thinks "pre-request" means "before the block" could plausibly
--      name.  *** RED ***: `LiveDrvBFD.agda:1295.1-23: error: [ShouldBeEmpty]
--      CliSendAdj NS.bcWcd x q′ should be empty, but the following constructor patterns
--      are valid: … CliSendAdj.csCD … when checking the clause left hand side
--      cliSend-idle-⊥ x q′ ()`, EXIT=42 — `bcWcd` is the source of the client-done
--      send, so a clause pinning the client anywhere but `bcIdle` costs the io FILL
--      class its free refutation.  (The READ direction's twin is F111, run at the up
--      hop on the identical statement, so it is not re-run here.)  Reverted by string
--      inversion.
cliSend-idle-⊥ : (x : Payload) (q′ : NS.BFcPos) → CliSendAdj NS.bcIdle x q′ → ⊥
cliSend-idle-⊥ x q′ ()

cliRead-idle-⊥ : (x : Payload) (q′ : NS.BFcPos) → CliReadAdj NS.bcIdle x q′ → ⊥
cliRead-idle-⊥ x q′ ()

-- the core at ABSTRACT positions — which is what lets the api class match
-- `BFCliDrvAdj`'s rows at all (a datatype whose indices are neutral terms cannot be
-- split on; `bfFresh-cliApi` is stated this way for the same reason)
DnIdlC : ConsPh → NS.BFcPos → Set
DnIdlC x ca = DnPre x → ca ≡ NS.bcIdle

-- *** THE api CLASS — the whole content of the factor, at six one-line clauses. ***
-- `dbReq` lands at `cp3`, `dbRecv` at `cp4`, `db45` at `cp5` and `dbCS56` at `cp6`:
-- all four are OUTSIDE the region, so the obligation is vacuous at the target.  The
-- two CS hops keep node D inside the region and hold its BF client LITERALLY
dnIdlC-api : (ca ca′ : NS.BFcPos) (x x′ : ConsPh)
           → BFCliDrvAdj ca x ca′ x′ → DnIdlC x ca → DnIdlC x′ ca′
dnIdlC-api _ _ _ _ (dbReq r)     h ()
dnIdlC-api _ _ _ _ (dbRecv b q′) h ()
dnIdlC-api _ _ _ _ (db45 q q′)   h ()
dnIdlC-api _ _ _ _ (dbCS01 q)    h g = h tt
dnIdlC-api _ _ _ _ (dbCS12 q)    h g = h tt
dnIdlC-api _ _ _ _ (dbCS56 q)    h ()

-- the carried form, at the leg's two slots
DnIdl : TwoLegs → SysState → Set
DnIdl l s = DnIdlC (phOf l s) (coarsenBFc (dnClient l s))

-- BASE — `initial` puts node D at `cp0`, INSIDE the guard, so this one owes the value:
-- both legs' down BF clients are `bcIdle` there
dnIdl-init : (l : TwoLegs) → DnIdl l initial
dnIdl-init legBD _ = refl
dnIdl-init legCD _ = refl

-- FRAME — the two components the clause reads, fixed (the drain and `break` shapes
-- keep all four node records literal, so both hold there)
dnIdl-frame : (l : TwoLegs) (s s′ : SysState)
            → phOf l s ≡ phOf l s′
            → coarsenBFc (dnClient l s) ≡ coarsenBFc (dnClient l s′)
            → DnIdl l s → DnIdl l s′
dnIdl-frame l s s′ deq keq h g = trans (sym keq) (h (subst DnPre (sym deq) g))

-- THE VISIBLE api CLASS at the state level — node D held both slots, or it fired and
-- §2c's producer gives the hop.  This is `LiveChanJoin.BfNodeD` exactly, which the
-- freshness clause already reads at the same site: the value is BOUND there and passed
-- twice (M-5), so this class costs the join ONE line
dnIdl-api : (l : TwoLegs) (s s′ : SysState)
          → ((phOf l s ≡ phOf l s′) × (dnClient l s ≡ dnClient l s′))
            ⊎ BFCliDrvAdj (coarsenBFc (dnClient l s)) (phOf l s)
                          (coarsenBFc (dnClient l s′)) (phOf l s′)
          → DnIdl l s → DnIdl l s′
dnIdl-api l s s′ (inj₁ (deq , keq)) = dnIdl-frame l s s′ deq (cong coarsenBFc keq)
dnIdl-api l s s′ (inj₂ adj)         = dnIdlC-api _ _ _ _ adj

-- THE io FILL CLASS — an io leaves every driver alone, so node D's phase is fixed and
-- its client either is too or fired a wire SEND, whose two sources are not `bcIdle`
dnIdl-fill : (l : TwoLegs) (s s′ : SysState) (x : Payload)
           → phOf l s ≡ phOf l s′
           → (coarsenBFc (dnClient l s) ≡ coarsenBFc (dnClient l s′))
             ⊎ CliSendAdj (coarsenBFc (dnClient l s)) x (coarsenBFc (dnClient l s′))
           → DnIdl l s → DnIdl l s′
dnIdl-fill l s s′ x deq (inj₁ keq) h = dnIdl-frame l s s′ deq keq h
dnIdl-fill l s s′ x deq (inj₂ adj) h g =
  ⊥-elim (cliSend-idle-⊥ x (coarsenBFc (dnClient l s′))
           (subst (λ z → CliSendAdj z x (coarsenBFc (dnClient l s′)))
                  (h (subst DnPre (sym deq) g)) adj))

-- … and the io READ CLASS, its mirror at the four client reads
dnIdl-read : (l : TwoLegs) (s s′ : SysState) (x : Payload)
           → phOf l s ≡ phOf l s′
           → (coarsenBFc (dnClient l s) ≡ coarsenBFc (dnClient l s′))
             ⊎ CliReadAdj (coarsenBFc (dnClient l s)) x (coarsenBFc (dnClient l s′))
           → DnIdl l s → DnIdl l s′
dnIdl-read l s s′ x deq (inj₁ keq) h = dnIdl-frame l s s′ deq keq h
dnIdl-read l s s′ x deq (inj₂ adj) h g =
  ⊥-elim (cliRead-idle-⊥ x (coarsenBFc (dnClient l s′))
           (subst (λ z → CliReadAdj z x (coarsenBFc (dnClient l s′)))
                  (h (subst DnPre (sym deq) g)) adj))

-- (B, cellCp3) … and the THIRD member: `DnIdl` walks the same down-BlockFetch hop as
-- the other two, so it folds here rather than becoming a ninth `LegJointU` factor
-- (T11h's rule again, third application)
BFJoint : TwoLegs → SysState → Set
BFJoint l s = LDB.DrvBF l s × BFFresh l s × DnIdl l s

-- BASE — all three halves at `initial`
bfJoint-init : (l : TwoLegs) → BFJoint l initial
bfJoint-init l = LDB.drvBF-init l , bfFresh-init l , dnIdl-init l

-- … and the ONE combinator the join needs
mkBFJoint : (l : TwoLegs) (s s′ : SysState)
          → (LDB.DrvBF l s → LDB.DrvBF l s′) → (BFFresh l s → BFFresh l s′)
          → (DnIdl l s → DnIdl l s′)
          → BFJoint l s → BFJoint l s′
mkBFJoint l s s′ f g k (db , fr , di) = f db , g fr , k di

-- the three projections
bfJoint⇒drv : (l : TwoLegs) (s : SysState) → BFJoint l s → LDB.DrvBF l s
bfJoint⇒drv l s (db , _) = db

bfJoint⇒fresh : (l : TwoLegs) (s : SysState) → BFJoint l s → BFFresh l s
bfJoint⇒fresh l s (_ , fr , _) = fr

bfJoint⇒dnIdl : (l : TwoLegs) (s : SysState) → BFJoint l s → DnIdl l s
bfJoint⇒dnIdl l s (_ , _ , di) = di

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `LiveDrvBF` — *** S1: THE BlockFetch DRIVER-TAIL COUPLING. ***
--
-- The cross-node api campaign's shared BlockFetch object: the relay driver's OWN
-- phase pins its DOWN-hop BlockFetch SERVER's position.  This is the direction
-- (driver phase ⇒ peer position) that this development had never proved — every
-- prior object runs occupancy ⇒ driver phase (`PipeInv.Coupled`,
-- `PipeSrvInv.SrvCoupled`) or is a parked premise in that direction
-- (`LiveTokenExcl.UpChainCp3`/`DnChainCp3`) — and it is the direction all nine
-- equations of `LiveRelayCS`'s api residual need.
--
-- *** WHAT IS HERE, AND WHAT IS DELIBERATELY NOT. ***  EIGHT funded arms since (T7):
-- two BlockFetch, six ChainSync, two of them REGIONS — and FOUR of the eight are ONE
-- CHAIN whose last link alone is a residual arm (the `cp2 … cp5` window; the paragraph
-- at the bottom of this header says why the other three exist).  On the BF axis, at
-- `producing b pp4` the leg's down BF server is at `bsBusy` — exactly
-- `LiveRelayCS.BFAt`'s `pp4` clause, T1's deliverable; at `producing b pp5` it is in
-- the REGION `{bsWsb, bsStream}` — T2's, and the paragraph below says why that is a
-- region and what turns it into `BFAt`'s `pp5` equation.  On the CS axis, at
-- `producing b pp1` the leg's down CS server is at `csCanAwait` (T5) and at
-- `producing b pp2` it is in the REGION `{csWar, csMust}` (T6d) — `LiveRelayCS.CSAt`'s
-- own two clauses, and the two paragraphs below say why the second is a region.  §1's
-- dispatch is the extension point: T8's `cp4` arm is a further FUNDED CLAUSE of it,
-- with its own per-class half below, and nothing but this module and `LiveChanJoin`'s
-- five arms moved when `pp5` landed (measured: `LiveChanJoin` ZERO edits at T2 as
-- well, and ZERO again at T6d — the `csDrv` selector is `_`-typed and adapts).
--
-- *** THE SHAPE, AND WHY IT IS THE TOTAL ONE (read this before quoting T1 on the
-- question — T1's own version of this note was WRONG, and T2 replaced the shape it
-- defended). ***  What T1 said is narrow and true: the CARRIED form
-- `DrvCp l s (relayOf l s)` cannot be preserved, because producing it at `s′` means
-- abstracting `relayOf l s′` — a defined application, not an explicit argument,
-- which the campaign's `blkA`-module rule forbids.  What T1 concluded from that —
-- that a total `CPPh` dispatch is unbuildable — is FALSE, and the review exhibited
-- the shape that is now below: the total dispatch on an EXPLICIT phase, carried
-- through the Π-bridge `DrvBF l s = (x : CPPh) → relayOf l s ≡ x → DrvCp l s x`,
-- which is `LiveRelayCS.coAt-split-at`'s own idiom (`:252`, re-derived by grep — the
-- review's `:315` is `relayCo-from`'s neighbourhood, not the signature) in the very
-- file this module discharges into.  Preservation never abstracts a defined
-- application: every dispatch is on `x`.
--
-- *** WHAT THE SWITCH BOUGHT (T2). ***  The type-level exhaustiveness guard is back:
-- a new `ConsPh`/`ProdPh` constructor is a COVERAGE ERROR at `DrvCp` and at
-- `drvCp-of` — the second of the two being the one that forces the DISCHARGE-or-
-- PREMISE decision to be taken rather than defaulted.  T1's record of implications
-- proved the identical content and was sound (`CoAt`/`CSAt`/`BFAt` and the three maps
-- of `LiveRelayCS` §3 were, and are, total anyway, so a new phase was already a
-- coverage error at six sites); what it gave up was that completeness guard, which
-- was carried as a standing risk (`STABR_STATUS.md` §4 RISKS item 7) until this
-- switch retired it — the item is GONE from RISKS now and its guidance sits at that
-- file's §5, first bullet, with the eight guard sites named.  Measured cost of the
-- switch: 43 net code lines, no consumer churn at all (`LiveChanJoin` and
-- `LiveRelayCS` see the same names at the same types), which is why the review put it
-- at "the last cheap moment".
--
-- *** THE FIVE STEP CLASSES, AND WHY FOUR OF THEM ARE CHEAP. ***  `bsBusy` is
-- entered by ONE row of `NodeSpecs.bfSnxt` (`bsAreq r + apiBF reqBFRange`,
-- `:596-600`) and left by TWO (`sendBFStartBatch`/`sendBFNoBlocks`, `:604-609`) —
-- all three api.  NO io row touches it, in either direction.  So:
--   · medium-τ and `break` frame (both fix every node record);
--   · the two io classes frame as well, and their proof is the REFUTATION of the
--     fired-row arm at `bsBusy`, off `LiveChanInv`'s own `SrvSendAdj`/`SrvReadAdj`
--     transcription — no new table reading;
--   · only the visible api class does work, and there the whole content is
--     `LiveLegApiCone.DnSrvDrv`: the phase/server pair across the step.
-- That asymmetry is also why `cp4` (T8) will be dearer: `bcIdle`'s region is NOT
-- io-closed, so its io arms need `H19`-style regions rather than a refutation.
--
-- *** AND WHY `pp5` IS A REGION, NOT A POSITION (T2). ***  `bsWsb` is entered by ONE
-- api row (`bsBusy + sendBFStartBatch`, `:604-605`) — the driver's OWN `pp4 → pp5`
-- step — and left by ONE io row (its `MsgStartBatch` wire-send, `:610-613`), which
-- lands at `bsStream`.  So at the instant the driver ENTERS `pp5` the server is at
-- `bsWsb`, not at `bsStream`, and no carried invariant can say `≡ bsStream` there.
-- What is carryable is the pair, and it is io-CLOSED as a pair: the one io row inside
-- it stays inside it (`srvSend-wsb-stream`), `bsStream` has no io row at all
-- (`srvSend-stream-⊥`), and neither end has an `output` row (`srvRead-*-⊥`).  The
-- residual's singleton equation is then one refutation away — `bsWsb` has an enabled
-- hidden τ at every stable state with an unbroken link, which is
-- `LiveSrvOpen.srvWsb-⊥` — and that refutation lives at the CONSUMER, because it is a
-- fact about `radec r` and not about a `SysState`.
--
-- The api class pays for `pp5` in one more way: at a `pp5` LANDING the arm needs the
-- server's row, and the cone's `DnSrvDrv` fixity arm is exactly the case it must
-- exclude — so T2 added the `sendBFStartBatch` label pin, the landing
-- (`LiveLegApiCone.SrvSbLand`/`DnSbLand`) and an ELEVENTH classifier component that
-- reports the SOURCE phase `pp4` with it.  That is what makes the arm below
-- self-feeding: it reads its own `pp4` clause at `s` to get the landing's antecedent.
--
-- *** (T5) AND THE ChainSync `pp1` ARM IS A CLAUSE OF THE SAME DISPATCH, NOT A
-- SIBLING MODULE. ***  The T5 verification priced the arm as a fresh `DrvCS` object
-- (its own Π bridge, `of`/`to`/`init`/`frame` and five class arms, ≈70-90 + ≈50-70);
-- extending §1's clause list instead costs the CLAUSE and the ARM and nothing else,
-- because the five step classes are the SAME five and the Π bridge is the same
-- bridge.  Measured: no consumer churn beyond one argument per arm, no new module
-- header, and `LiveChanJoin` keeps ONE carried factor.  The name `DrvBF` is kept
-- (churning it would touch every consumer for nothing) but the object is now the
-- relay driver-tail coupling for BOTH protocols' funded arms, and its KEEP-IN-SYNC
-- partner is `LiveRelayCS.BFAt` *and* `CSAt`: every funded clause below is the clause
-- one of them gave up at that shape.
--
-- *** WHY `pp1` IS THE CHEAP CS ARM. ***  `csCanAwait` is entered by exactly ONE row
-- (`csSnxt csAreq + apiCS reqCSRequestNext`, `NodeSpecs:428-430` — T5's per-key pin
-- `LiveCSRow.cssReqLands`) and left only by its three api rows, so it is io-CLOSED
-- (`LiveCSRow` §4b's four refutations) exactly as `bsBusy` is: the two io classes
-- REFUTE the fired-row arm and only the visible api class does work.  The api arm's
-- whole content is the cone's `LiveLegApiCone.DnCsDrv` — the `pp1` twin of
-- `DnSrvDrv`, whose landing half is already APPLIED (§2b″ does the table reading at
-- the bundle), which is why this arm needs no source-phase antecedent at all.  The io
-- fact it reads is grant #11's fourth channel (`LiveLegIoCone.CssRowP`).
--
-- *** (T6d) AND `pp2` IS A CS REGION, FOR `pp5`'s REASON EXACTLY. ***  `csWar` is
-- entered by ONE api row (`csCanAwait + apiCS sendCSAwaitReply`, `NodeSpecs:445-446`
-- — T6's per-key pin `LiveCSRow.cssAwaitLands`) — the driver's OWN `pp1 → pp2` step —
-- and left by ONE io row, the server's `MsgCSAwaitReply` wire-send (`:472-477`), which
-- lands at `csMust`.  So at the instant the driver ENTERS `pp2` the server is at
-- `csWar`, and no carried invariant can say `≡ csMust` there.  What is carryable is
-- the PAIR, and it is io-CLOSED as a pair: `cssWar-in-must` keeps the one io row
-- inside it, `cssWar-out-⊥`/`cssMust-in-⊥`/`cssMust-out-⊥` refute the other three
-- directions (`LiveCSRow` §4c).  The residual's singleton `≡ csMust` is then one
-- refutation away — `LiveSrvOpen.csWar-⊥`, which lives at the CONSUMER because it is a
-- fact about `radec r`.  The api arm needs the cone's SECOND CS landing for `pp5`'s
-- other reason too (`DnCsDrv`'s fixity arm is the case the arm must exclude), and that
-- is the T6d landing family: `LiveLegApiCone` §1c‴/§2b‴, `DnCsAwLand`, and a
-- THIRTEENTH classifier component.  Unlike `pp5`'s it needs NO source phase.
--
-- *** (T7) AND THE `cp5` CHAIN IS THE FIRST OBJECT HERE ON THE **CONSUME** SIDE, AND
-- THE FIRST WHOSE PEER IS A **CLIENT**. ***  Everything above watches the leg's DOWN-hop
-- server against a `producing` sub-phase; `cp5` watches the leg's UP-hop CS CLIENT
-- against a `consuming` one, and three things follow that a reader should not have to
-- rediscover:
--
--   (1) *** IT IS A CHAIN OF FOUR AND NOT ONE ARM. ***  `ccIdle` is entered by ONE row
--       reachable here — `ccArf ht + apiCS recvCSRollforward` (`NodeSpecs:361-365`,
--       T5's per-key pin `LiveCSRow.cscRfwLands`) — and that row is the relay's own
--       `cp1 → cp2` step.  The residual names `cp5`, THREE hops later.  The three hops
--       in between (`sendBFRequestRange`, `recvBFBlock`, `sendBFClientDone`,
--       `SysNode.decCons:938-957`) are BlockFetch api events that no `csCnxt` row
--       answers, so they hold the client where it is — but an induction cannot state
--       "held" without a clause at the source sub-phase, and that is why `cp2`, `cp3`
--       and `cp4` are funded clauses with no residual partner.  *** They are carriers.
--       Do not delete one for lacking a `CSAt` twin. ***
--
--   (2) *** IT IS A POSITION, SO IT COSTS NO SHARPENING AND NO NEW PREMISE. ***  The one
--       row into `ccIdle` lands there and `ccIdle` has no io row in either direction
--       (`LiveCSRow` §4b's `cscIdle-in-⊥`/`cscIdle-out-⊥`), so the coupling carries the
--       residual's own equation and `coAt-split-at` gains no third unconditional
--       premise.  The T6d review §4(b) predicted exactly this and declined a refactor on
--       the strength of it; the prediction held.
--
--   (3) *** THE COST IS THE SOURCE PHASE, WHICH BOTH LANDED CS ARMS ESCAPED. ***  Three
--       of the four api arms read their own clause one sub-phase back, so they need the
--       cone to report where the step CAME FROM — `DnSbLand`'s shape (T2), not
--       `DnCsReqLand`'s.  In the cone that report is free (its classifier is total on the
--       phase, so the source is a literal pattern); at the consumer it is one `let` per
--       arm.  The io arms need none of it: a driver phase is FIXED across an io step, so
--       ONE io lemma per direction serves all four sub-phases.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `funext`, and no
-- `with` in anything whose type mentions an imported `blkA`-parameterised
-- predicate — every dispatch is on an EXPLICIT argument (the campaign's
-- `blkA`-module rule).
------------------------------------------------------------------------

open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit using ( ⊤; tt )
open import Data.Maybe using ( just )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Product using ( _,_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; subst; cong )

-- the `_≟_` instances `bfSnxt`'s own key and payload gates are stated at — the
-- same set `LiveChanInv` §4b needs, and for the same reason (a `with`-abstraction
-- here has to see the table's comparisons)
open import Class.DecEq using ( DecEq; _≟_ )
open import Class.DecEq.Instances using ( DecEq-Fin )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBF
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p
  using ( Link; input; output; apiBF; ApiBFCar; reqBFRange )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; ChainRange; DecEq-ChainRange )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; hi; IDs; DecEq-Dir
        ; N2N_ChainSync; N2N_BlockFetch; N2N_KeepAlive; N2N_TxSubmission
        ; N2N_LeiosNotify; N2N_LeiosFetch )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial; nB; nC )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
-- the relay driver's phase datatype, UNQUALIFIED: §1's dispatch writes all
-- seventeen shapes out, so the clause heads have to be readable
open SN using ( CPPh; consuming; producing
              ; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              ; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9 )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  -- (T7) `coarsenCSc` is the CS CLIENT's coarsening — the `cp5` chain's own
  -- (B, cellCp3) … and `coarsenBFc` is the BF CLIENT's, which §3's two new selectors
  -- state their answer at
  using ( coarsenBFs; coarsenBFc; coarsenCSs; coarsenCSc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( relayOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  -- (T7) the leg's UPSTREAM link, so the `cp5` chain's arms are stated hop-generically
  -- (`upLink legBD = linkAB`, `upLink legCD = linkAC`)
  using ( dnLink; upLink )
-- the io axis: the four peers' fired-row facts (grant #7's cone slots), and the
-- two io adjacency transcriptions the refutations at `bsBusy` run on
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone blkA as LIC
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanInv blkA
  -- (T2) `ssSB` is the wire-send row that closes the `pp5` region, and it is
  -- MATCHED below, so the constructor has to be in scope by name (measured: without
  -- it the clause head reads as a pattern VARIABLE and the target is unconstrained —
  -- `[PatternShadowsConstructor]` plus an `[UnequalTerms]` at the `refl`)
  -- (B, cellCp3) … and the CLIENT's two, for §3's two new selectors: the same pair of
  -- transcriptions at the other role
  using ( SrvSendAdj; SrvReadAdj; srvSendRow; srvReadRow; ssSB
        ; CliSendAdj; CliReadAdj; cliSendRow; cliReadRow )
-- (T5) the CS axis: the down-hop CS SERVER slot accessor (the SAME term
-- `LiveRelayCS.CSAt`'s `pp1` clause reads, which is what makes the discharge
-- convertible — a local twin would not be), and the two io refutations plus the
-- per-key landing the arm rests on
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveRelayOpen blkA
  -- (T7) … and the leg's UP-hop CS CLIENT slot accessor beside it, the term
  -- `LiveRelayCS.CSAt`'s `cp5` clause reads — for `dnCSs`'s reason exactly: a local twin
  -- would not be convertible with the residual's own statement
  using ( dnCSs; upCSc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCSRow blkA
  using ( cssCanAwait-in-⊥; cssCanAwait-out-⊥
        -- (T6d) §4c's four io facts about the `pp2` REGION: `csWar`'s ONE io row
        -- lands INSIDE it (at `csMust`), `csWar` has no io READ row, and `csMust`
        -- is io-CLOSED in both directions
        ; cssWar-in-must; cssWar-out-⊥; cssMust-in-⊥; cssMust-out-⊥
        -- (T7) … and §4b's two CLIENT io refutations: `ccIdle` has no wire row in
        -- either direction, at any key and on any channel, so the `cp5` chain's io
        -- arms are `csCanAwait`'s refutations and not `csWar`'s region
        ; cscIdle-in-⊥; cscIdle-out-⊥ )
-- the api axis: the whole content of S1's visible arm
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiCone blkA as LAC

------------------------------------------------------------------------
-- §1  THE COUPLING.
------------------------------------------------------------------------

-- *** S1 — the leg's BlockFetch driver-tail coupling, PER SUB-PHASE. ***  A TOTAL
-- dispatch on an EXPLICIT `CPPh`: all seventeen shapes written out, no catch-all,
-- `⊤` at every sub-phase the campaign has not funded and the FUNDED ones stating
-- exactly the `LiveRelayCS` residual arm they discharge.  Totality is the point — a
-- new `ConsPh`/`ProdPh` constructor is a COVERAGE ERROR here, exactly as it is at
-- `CoAt`/`CSAt`/`BFAt` and the three maps of `LiveRelayCS` §3, so the question "does
-- S1 DISCHARGE the new sub-phase, or does `BFAt` PREMISE it?" cannot be answered by
-- silence.
--
-- *** KEEP IN SYNC with `LiveRelayCS.BFAt` **AND** `LiveRelayCS.CSAt`. ***  Every
-- funded clause below is the clause ONE OF THOSE TWO gave up at that shape, verbatim:
-- `pp4` and `pp5` came from `BFAt` (T1, T2) and (T5) `pp1` and (T6d) `pp2` came from
-- `CSAt` — this dispatch has covered BOTH protocols since the ChainSync arm landed as
-- a clause of it rather than as a sibling module (the header's own paragraph says why).
-- (T7) `cp5` came from `CSAt` too, and with it its THREE CARRIERS `cp2`/`cp3`/`cp4`,
-- which `CSAt` never premised — *** so from T7 on the funded clauses of this dispatch
-- are NOT in bijection with the residual's, and a sync sweep must not "tidy" a carrier
-- away for having no partner. ***  The four form ONE chain and only its last link is a
-- residual arm.
-- `coAt-split-at` is the machine check for both halves and it stops typechecking if
-- EITHER side drifts (F12 and F18 for the BF arms, F26/F43/F47 for the CS ones — F43 is
-- the `pp2` one and F47 the `cp5` one).  A sync
-- sweep that greps only for `BFAt` here would have missed the `pp1` clause four lines
-- below — which is the rot this marker exists to prevent (review I-1).
DrvCp : (l : TwoLegs) (s : SysState) → CPPh → Set
DrvCp l s (consuming _ cp0) = ⊤
DrvCp l s (consuming _ cp1) = ⊤
-- (T7) the FIFTH, SIXTH, SEVENTH and EIGHTH funded arms, and the campaign's first on
-- the CONSUME side: from the instant the relay's `cp1 → cp2` step fires
-- `recvCSRollforward` at its UP link, the leg's UP-hop CS CLIENT sits at `ccIdle`
-- (`LiveCSRow.cscRfwLands`) and stays there for the whole `cp2 … cp5` window, because
-- the three hops inside it fire BlockFetch api events that no `csCnxt` row answers and
-- `ccIdle` has no io row at all (`cscIdle-in-⊥`/`cscIdle-out-⊥`).  Only the LAST of the
-- four is a residual arm — it is exactly `LiveRelayCS.CSAt`'s `cp5` clause; the other
-- three are its CARRIERS and exist so the induction has somewhere to stand.  A POSITION,
-- not a region: the one row into `ccIdle` lands there, so nothing needs sharpening at
-- the consumer (unlike `pp2`/`pp5`, and this is why `cp5` needs no `csWar-⊥` twin and
-- adds NO unconditional premise to `coAt-split-at` — the T6d review §4(b) called that
-- and it held).
DrvCp l s (consuming _ cp2) = coarsenCSc (upCSc l s) ≡ NS.ccIdle
DrvCp l s (consuming _ cp3) = coarsenCSc (upCSc l s) ≡ NS.ccIdle
DrvCp l s (consuming _ cp4) = coarsenCSc (upCSc l s) ≡ NS.ccIdle
DrvCp l s (consuming _ cp5) = coarsenCSc (upCSc l s) ≡ NS.ccIdle
DrvCp l s (consuming _ cp6) = ⊤
DrvCp l s (producing _ pp0) = ⊤
-- (T5) the THIRD funded arm, and the first on the ChainSync axis: at `producing b
-- pp1` the leg's DOWN CS server is at `csCanAwait` — exactly `LiveRelayCS.CSAt`'s
-- `pp1` clause
DrvCp l s (producing _ pp1) = coarsenCSs (dnCSs l s) ≡ NS.csCanAwait
-- (T6d) the FOURTH funded arm, the second on the ChainSync axis, and the second
-- REGION: at `producing b pp2` the leg's DOWN CS server is in `{csWar, csMust}` —
-- the api step that ENTERS `pp2` lands it at `csWar` (`LiveCSRow.cssAwaitLands`) and
-- only the server's own `MsgCSAwaitReply` wire-send carries it on to `csMust`
-- (`cssWar-in-must`), so no carried invariant can say `≡ csMust` at that instant.
-- `LiveRelayCS.csRegion⇒must` sharpens it, on `LiveSrvOpen.csWar-⊥`
DrvCp l s (producing _ pp2) = (coarsenCSs (dnCSs l s) ≡ NS.csWar)
                            ⊎ (coarsenCSs (dnCSs l s) ≡ NS.csMust)
DrvCp l s (producing _ pp3) = ⊤
-- (T1) the first funded arm: at `producing b pp4` the leg's down BF server is `bsBusy`
DrvCp l s (producing _ pp4) = coarsenBFs (dnSrv l s) ≡ NS.bsBusy
-- (T2) the second funded arm, and it is a REGION rather than a position (the header's
-- `pp5` paragraph says why; `LiveRelayCS.region⇒stream` is what sharpens it)
DrvCp l s (producing _ pp5) = (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
                            ⊎ (coarsenBFs (dnSrv l s) ≡ NS.bsStream)
DrvCp l s (producing _ pp6) = ⊤
DrvCp l s (producing _ pp7) = ⊤
DrvCp l s (producing _ pp8) = ⊤
DrvCp l s (producing _ pp9) = ⊤

-- … and the coupling CARRIED, at the driver's ACTUAL phase, through the Π-bridge:
-- this is `LiveRelayCS.coAt-split-at`'s own idiom (`:252`, `(x : CPPh) → relayOf l s
-- ≡ x → …`) and it is what makes the total shape PRESERVABLE — producing the
-- coupling at `s′` dispatches on the EXPLICIT `x`, never on the defined application
-- `relayOf l s′`, so the campaign's `blkA`-module rule is satisfied by construction.
DrvBF : TwoLegs → SysState → Set
DrvBF l s = (x : CPPh) → relayOf l s ≡ x → DrvCp l s x

-- the bridge IN — the funded arms are ALL a producer of the coupling has to supply;
-- the sixteen unfunded shapes are `tt`.  (This clause list is the second site a new
-- sub-phase breaks, and the one that forces the DISCHARGE-or-PREMISE decision: a new
-- funded arm has to arrive here as a new argument.)
--
-- *** (T7 fix round) THE EIGHT WITNESSES ARE NAMED AFTER THEIR SUB-PHASES. ***  `p4 p5
-- p1 p2` are the four with a `LiveRelayCS` partner (`BFAt`'s `pp4`/`pp5`, `CSAt`'s
-- `pp1`/`pp2`); `c2 c3 c4 c5` are the `cp5` chain, of which only `c5` has a partner and
-- `c2`/`c3`/`c4` are its carriers.  They were `f g h k n₂ n₃ n₄ n₅` until the T7 review
-- ruled the rename in: the argument ORDER is historical (arms in the order they were
-- funded, appended, never reordered — reordering would silently break every construction
-- site), so the names are the only place the partner/carrier split can be read off, and
-- an opaque name at a list this long is where a mis-wiring hides.  A PURE RENAME: zero
-- net lines, zero proof change, and the endpoint was rechecked because it changes this
-- module's interface hash.
drvCp-of : (l : TwoLegs) (s : SysState)
         → ((b : Block₃) → relayOf l s ≡ producing b pp4
                         → coarsenBFs (dnSrv l s) ≡ NS.bsBusy)
         → ((b : Block₃) → relayOf l s ≡ producing b pp5
                         → (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
                           ⊎ (coarsenBFs (dnSrv l s) ≡ NS.bsStream))
         -- (T5) the CS arm arrives here as a THIRD argument, which is the point of
         -- the clause list: a new funded arm cannot be defaulted to `⊤` by silence
         → ((b : Block₃) → relayOf l s ≡ producing b pp1
                         → coarsenCSs (dnCSs l s) ≡ NS.csCanAwait)
         -- (T6d) … and the `pp2` REGION as a FOURTH, for the same reason
         → ((b : Block₃) → relayOf l s ≡ producing b pp2
                         → (coarsenCSs (dnCSs l s) ≡ NS.csWar)
                           ⊎ (coarsenCSs (dnCSs l s) ≡ NS.csMust))
         -- (T7) … and the `cp5` CHAIN as a FIFTH to EIGHTH.  FOUR arguments and not
         -- one, even though the four state the SAME equation: they are indexed at four
         -- different sub-phases, so a producer that can answer three of them and not
         -- the fourth is a real possibility and the clause list is what makes that a
         -- type error rather than a silent `⊤`.  (Collapsing them behind a `CsWin`
         -- witness datatype was considered and declined — it would hide exactly the
         -- per-sub-phase obligation this list exists to expose.)
         → ((b : Block₃) → relayOf l s ≡ consuming b cp2
                         → coarsenCSc (upCSc l s) ≡ NS.ccIdle)
         → ((b : Block₃) → relayOf l s ≡ consuming b cp3
                         → coarsenCSc (upCSc l s) ≡ NS.ccIdle)
         → ((b : Block₃) → relayOf l s ≡ consuming b cp4
                         → coarsenCSc (upCSc l s) ≡ NS.ccIdle)
         → ((b : Block₃) → relayOf l s ≡ consuming b cp5
                         → coarsenCSc (upCSc l s) ≡ NS.ccIdle)
         → DrvBF l s
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (consuming _ cp0) _  = tt
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (consuming _ cp1) _  = tt
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (consuming b cp2) eq = c2 b eq
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (consuming b cp3) eq = c3 b eq
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (consuming b cp4) eq = c4 b eq
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (consuming b cp5) eq = c5 b eq
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (consuming _ cp6) _  = tt
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing _ pp0) _  = tt
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing b pp1) eq = p1 b eq
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing b pp2) eq = p2 b eq
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing _ pp3) _  = tt
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing b pp4) eq = p4 b eq
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing b pp5) eq = p5 b eq
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing _ pp6) _  = tt
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing _ pp7) _  = tt
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing _ pp8) _  = tt
drvCp-of l s p4 p5 p1 p2 c2 c3 c4 c5 (producing _ pp9) _  = tt

-- … and the bridge OUT at the `pp4` arm: the consumer's shape is the equation under
-- the phase that fires it, which is the Π instantiated at that phase
drvCp-to : (l : TwoLegs) (s : SysState) → DrvBF l s
         → (b : Block₃) → relayOf l s ≡ producing b pp4
         → coarsenBFs (dnSrv l s) ≡ NS.bsBusy
drvCp-to l s g b eq = g (producing b pp4) eq

-- … and at the `pp5` arm
drvCp-to5 : (l : TwoLegs) (s : SysState) → DrvBF l s
          → (b : Block₃) → relayOf l s ≡ producing b pp5
          → (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
            ⊎ (coarsenBFs (dnSrv l s) ≡ NS.bsStream)
drvCp-to5 l s g b eq = g (producing b pp5) eq

-- … and at the (T5) `pp1` arm
drvCp-to1 : (l : TwoLegs) (s : SysState) → DrvBF l s
          → (b : Block₃) → relayOf l s ≡ producing b pp1
          → coarsenCSs (dnCSs l s) ≡ NS.csCanAwait
drvCp-to1 l s g b eq = g (producing b pp1) eq

-- … and at the (T6d) `pp2` arm, whose field is the CS REGION
drvCp-to2 : (l : TwoLegs) (s : SysState) → DrvBF l s
          → (b : Block₃) → relayOf l s ≡ producing b pp2
          → (coarsenCSs (dnCSs l s) ≡ NS.csWar)
            ⊎ (coarsenCSs (dnCSs l s) ≡ NS.csMust)
drvCp-to2 l s g b eq = g (producing b pp2) eq

-- … and (T7) at the `cp5` chain's four arms.  One bridge per sub-phase, for
-- `drvCp-of`'s reason: `DrvCp` reduces only at a CONSTRUCTOR phase, so a single
-- phase-parametric bridge would not typecheck at any of the four
drvCp-toC2 : (l : TwoLegs) (s : SysState) → DrvBF l s
           → (b : Block₃) → relayOf l s ≡ consuming b cp2
           → coarsenCSc (upCSc l s) ≡ NS.ccIdle
drvCp-toC2 l s g b eq = g (consuming b cp2) eq

drvCp-toC3 : (l : TwoLegs) (s : SysState) → DrvBF l s
           → (b : Block₃) → relayOf l s ≡ consuming b cp3
           → coarsenCSc (upCSc l s) ≡ NS.ccIdle
drvCp-toC3 l s g b eq = g (consuming b cp3) eq

drvCp-toC4 : (l : TwoLegs) (s : SysState) → DrvBF l s
           → (b : Block₃) → relayOf l s ≡ consuming b cp4
           → coarsenCSc (upCSc l s) ≡ NS.ccIdle
drvCp-toC4 l s g b eq = g (consuming b cp4) eq

drvCp-toC5 : (l : TwoLegs) (s : SysState) → DrvBF l s
           → (b : Block₃) → relayOf l s ≡ consuming b cp5
           → coarsenCSc (upCSc l s) ≡ NS.ccIdle
drvCp-toC5 l s g b eq = g (consuming b cp5) eq

-- the `pp5` REGION rides a server equation — the `⊎` has to be mapped, and a named
-- helper is what keeps the five class arms one-liners
region-cong : {q q′ : NS.BFsPos} → q ≡ q′
            → (q ≡ NS.bsWsb) ⊎ (q ≡ NS.bsStream)
            → (q′ ≡ NS.bsWsb) ⊎ (q′ ≡ NS.bsStream)
region-cong eq (inj₁ h) = inj₁ (trans (sym eq) h)
region-cong eq (inj₂ h) = inj₂ (trans (sym eq) h)

-- (T6d) … and the `pp2` REGION's own mapper, at the CS server's positions.  A second
-- copy rather than one polymorphic helper: `region-cong`'s two targets are `BFsPos`
-- literals and the disjunction is written out, not abstracted (the REUSE CAVEAT at
-- `drvBF-fill-at5` says why that is deliberate)
csRegion-cong : {q q′ : NS.CSsPos} → q ≡ q′
              → (q ≡ NS.csWar) ⊎ (q ≡ NS.csMust)
              → (q′ ≡ NS.csWar) ⊎ (q′ ≡ NS.csMust)
csRegion-cong eq (inj₁ h) = inj₁ (trans (sym eq) h)
csRegion-cong eq (inj₂ h) = inj₂ (trans (sym eq) h)

-- BASE — at `initial` the relay driver is CONSUMING, so every funded arm's
-- antecedent is uninhabited at both legs (the leg has to be a constructor for
-- `relayOf` to reduce to the node record's `cp` slot).
-- (T7) *** AND THE FOUR NEW ARMS ARE UNINHABITED FOR A DIFFERENT REASON, WHICH IS WHY
-- THIS LINE IS STILL FOUR `(λ b ())` LONGER RATHER THAN FOUR PROOFS. ***  The four
-- `producing` arms are refuted because `initial`'s driver is CONSUMING; the four new
-- ones are `consuming` arms, so they are refuted by the SUB-PHASE instead — `initial`
-- puts both relays at `consuming blkA cp0` (`SysNode:1078`, `:1124`), and `cp0 ≢ cpN`
-- for each of the four.  Same `()`, different absurdity; do not read the uniform
-- appearance as one argument.
drvBF-init : (l : TwoLegs) → DrvBF l initial
drvBF-init legBD = drvCp-of legBD initial (λ b ()) (λ b ()) (λ b ()) (λ b ())
                             (λ b ()) (λ b ()) (λ b ()) (λ b ())
drvBF-init legCD = drvCp-of legCD initial (λ b ()) (λ b ()) (λ b ()) (λ b ())
                             (λ b ()) (λ b ()) (λ b ()) (λ b ())

-- FRAME — the coupling reads exactly two components, so a step fixing both
-- carries it (the `chan-frame` shape at the driver tail; the server's equation is
-- taken COARSE, which is all the field mentions)
drvBF-frame : (l : TwoLegs) (s s′ : SysState)
            → relayOf l s ≡ relayOf l s′
            → coarsenBFs (dnSrv l s) ≡ coarsenBFs (dnSrv l s′)
            -- (T5) the coupling now reads THREE components, so the frame carries the
            -- CS server's coarse equation beside the BF server's
            → coarsenCSs (dnCSs l s) ≡ coarsenCSs (dnCSs l s′)
            -- (T7) … and FOUR, the fourth being the leg's UP-hop CS CLIENT.  All four
            -- of the `cp5` chain's arms ride this one equation
            → coarsenCSc (upCSc l s) ≡ coarsenCSc (upCSc l s′)
            → DrvBF l s → DrvBF l s′
drvBF-frame l s s′ peq seq ceq keq db =
  drvCp-of l s′ (λ b eq → trans (sym seq) (drvCp-to l s db b (trans peq eq)))
                (λ b eq → region-cong seq (drvCp-to5 l s db b (trans peq eq)))
                (λ b eq → trans (sym ceq) (drvCp-to1 l s db b (trans peq eq)))
                -- (T6d) the `pp2` REGION rides the SAME CS equation the `pp1`
                -- position does, mapped rather than transported
                (λ b eq → csRegion-cong ceq (drvCp-to2 l s db b (trans peq eq)))
                -- (T7) the chain's four arms are POSITIONS, so all four transport
                (λ b eq → trans (sym keq) (drvCp-toC2 l s db b (trans peq eq)))
                (λ b eq → trans (sym keq) (drvCp-toC3 l s db b (trans peq eq)))
                (λ b eq → trans (sym keq) (drvCp-toC4 l s db b (trans peq eq)))
                (λ b eq → trans (sym keq) (drvCp-toC5 l s db b (trans peq eq)))

-- (T5) the leg's down-hop CS SERVER is fixed whenever the two relay node RECORDS
-- are — the `break`/drain shape, where every node record is a literal.  Stated here
-- rather than at the consumer because `dnCSs` is in scope here and the consumer's
-- `LDB.`-qualified view does not re-export it.
dnCSs-fix : (l : TwoLegs) (s s′ : SysState)
          → nB s ≡ nB s′ → nC s ≡ nC s′ → dnCSs l s ≡ dnCSs l s′
dnCSs-fix legBD s s′ bq cq = cong SN.NodeStateB.csS-BD bq
dnCSs-fix legCD s s′ bq cq = cong SN.NodeStateC.csS-CD cq

-- (T7) … and the leg's UP-hop CS CLIENT is fixed by the same two record equations —
-- `dnCSs-fix`'s twin one hop up, stated here for its reason (`upCSc` is in scope here
-- and the consumer's `LDB.`-qualified view does not re-export it)
upCSc-fix : (l : TwoLegs) (s s′ : SysState)
          → nB s ≡ nB s′ → nC s ≡ nC s′ → upCSc l s ≡ upCSc l s′
upCSc-fix legBD s s′ bq cq = cong SN.NodeStateB.csC-AB bq
upCSc-fix legCD s s′ bq cq = cong SN.NodeStateC.csC-AC cq

-- the relay driver's phase is FIXED across an io step: the io cone reports BOTH
-- relay nodes' `cp` slots, and this is the per-leg selector for them
relayFix-of : (l : TwoLegs) (s s′ : SysState)
            → SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB s′)
            → SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC s′)
            → relayOf l s ≡ relayOf l s′
relayFix-of legBD s s′ bq cq = bq
relayFix-of legCD s s′ bq cq = cq

------------------------------------------------------------------------
-- §2  THE ONE TABLE FACT — the `reqBFRange` LANDING.
--
-- *** KEEP IN SYNC with `NodeSpecs.bfSnxt`'s third row (`:596-600`) and with
-- `LiveChanInv.srvApiRow`'s eight clauses at `bsAreq r` (`:660-673`, of which ONE is
-- the `reqBFRange` row; `srvApiRow` has three `reqBFRange` clauses in all —
-- `:667`, `:679`, `:695`). ***  `bfSnxt`
-- has exactly ONE `reqBFRange` row — `bsAreq r + apiBF reqBFRange → bsBusy` — so a
-- fired `reqBFRange` at a server's own key LANDS at `bsBusy` whatever the source
-- position was.
--
-- ONE DELIBERATE DEVIATION from `srvApiRow`, and it is the reason this lemma
-- exists at all: the conclusion is the LANDING (`sa′ ≡ bsBusy`), not the
-- `SrvApiAdj`.  The adjacency datatype has FORGOTTEN the tag — `saReq`, `saSB`,
-- `saNB` all live in it — so `SrvApiAdj sa sa′` cannot deliver the successor from
-- a tag pin, and a re-sync must not "simplify" this into a call to `srvApiRow`.
-- The nine absurd clauses are the same nine positions `srvApiRow` refutes.
------------------------------------------------------------------------

-- a fired `reqBFRange` row at the server's own key lands at `bsBusy`
srvReqLands : (i : Link) (d : Dir) (sa : NS.BFsPos) (v : ChainRange) (sa′ : NS.BFsPos)
            → NS.bfSnxt i d sa (ApiBFCar reqBFRange , apiBF i d reqBFRange) v ≡ just sa′
            → sa′ ≡ NS.bsBusy
srvReqLands i d NS.bsIdle     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvReqLands i d NS.bsBusy     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvReqLands i d NS.bsDdone    v sa′ eq = ⊥-elim (nothing-absurd eq)
srvReqLands i d NS.bsWsb      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvReqLands i d NS.bsStream   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvReqLands i d NS.bsWnb      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvReqLands i d (NS.bsWblk b) v sa′ eq = ⊥-elim (nothing-absurd eq)
srvReqLands i d NS.bsWbd      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvReqLands i d NS.bsTerm     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvReqLands i d (NS.bsAreq r) v sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl with v ≟ r
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes _   = sym (just-injective eq)

-- no `SrvSendAdj` leaves `bsBusy` — `bfSnxt`'s `bsBusy` rows are the two api ones
srvSend-busy-⊥ : {x : Payload} {q : NS.BFsPos} → SrvSendAdj NS.bsBusy x q → ⊥
srvSend-busy-⊥ ()

-- … and no `SrvReadAdj` does either
srvRead-busy-⊥ : {x : Payload} {q : NS.BFsPos} → SrvReadAdj NS.bsBusy x q → ⊥
srvRead-busy-⊥ ()

-- *** (T2) THE ROW THAT CLOSES THE `pp5` REGION. ***  `bsWsb` has exactly ONE io
-- row — the server's own `MsgStartBatch` wire-send, `ssSB` — and it lands INSIDE the
-- region, at `bsStream`.  This is the whole reason `pp5`'s clause is a region and
-- not a position: unlike `bsBusy`, `bsWsb` is not io-closed on its own.
srvSend-wsb-stream : {x : Payload} {q : NS.BFsPos} → SrvSendAdj NS.bsWsb x q
                   → q ≡ NS.bsStream
srvSend-wsb-stream ssSB = refl

-- … and the region's OTHER end is io-closed: `bsStream`'s two rows are api
srvSend-stream-⊥ : {x : Payload} {q : NS.BFsPos} → SrvSendAdj NS.bsStream x q → ⊥
srvSend-stream-⊥ ()

-- no `SrvReadAdj` leaves either end of the region (`bfSnxt`'s two `output` rows are
-- both at `bsIdle`), so the READ class refutes the fired-row arm at both disjuncts
srvRead-wsb-⊥ : {x : Payload} {q : NS.BFsPos} → SrvReadAdj NS.bsWsb x q → ⊥
srvRead-wsb-⊥ ()

srvRead-stream-⊥ : {x : Payload} {q : NS.BFsPos} → SrvReadAdj NS.bsStream x q → ⊥
srvRead-stream-⊥ ()

------------------------------------------------------------------------
-- §3  THE io ROW, REDUCED.  `LiveLegIoCone.SrvRowP` is LABEL-directed, so at a
-- variable `IDs` it does not reduce at all and the two io arms cannot case on it.
-- These two selectors do the channel dispatch ONCE per direction, at an abstract
-- key, and hand back either the peer's fixity or its io ADJACENCY — after which
-- the arms are three lines each.
------------------------------------------------------------------------

-- the FILL direction (`input` at the hop's key)
srvFill-adj : (k : Link) (kd : Dir) (bfs bfs′ : SN.BFsPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
            → LIC.SrvRowP k kd bfs bfs′ (input l₀ d₀ id₀) x
            → (bfs ≡ bfs′) ⊎ SrvSendAdj (coarsenBFs bfs) x (coarsenBFs bfs′)
srvFill-adj k kd bfs bfs′ l₀ d₀ N2N_BlockFetch x (inj₁ (eq , _)) = inj₁ eq
srvFill-adj k kd bfs bfs′ l₀ d₀ N2N_BlockFetch x (inj₂ (refl , refl , row)) =
  inj₂ (srvSendRow k kd (coarsenBFs bfs) x (coarsenBFs bfs′) row)
srvFill-adj k kd bfs bfs′ l₀ d₀ N2N_ChainSync    x (inj₁ (eq , _)) = inj₁ eq
srvFill-adj k kd bfs bfs′ l₀ d₀ N2N_KeepAlive    x (inj₁ (eq , _)) = inj₁ eq
srvFill-adj k kd bfs bfs′ l₀ d₀ N2N_TxSubmission x (inj₁ (eq , _)) = inj₁ eq
srvFill-adj k kd bfs bfs′ l₀ d₀ N2N_LeiosNotify  x (inj₁ (eq , _)) = inj₁ eq
srvFill-adj k kd bfs bfs′ l₀ d₀ N2N_LeiosFetch   x (inj₁ (eq , _)) = inj₁ eq

-- … and the READ direction (`output` at the hop's key)
srvRead-adj : (k : Link) (kd : Dir) (bfs bfs′ : SN.BFsPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
            → LIC.SrvRowP k kd bfs bfs′ (output l₀ d₀ id₀) x
            → (bfs ≡ bfs′) ⊎ SrvReadAdj (coarsenBFs bfs) x (coarsenBFs bfs′)
srvRead-adj k kd bfs bfs′ l₀ d₀ N2N_BlockFetch x (inj₁ (eq , _)) = inj₁ eq
srvRead-adj k kd bfs bfs′ l₀ d₀ N2N_BlockFetch x (inj₂ (refl , refl , row)) =
  inj₂ (srvReadRow k kd (coarsenBFs bfs) x (coarsenBFs bfs′) row)
srvRead-adj k kd bfs bfs′ l₀ d₀ N2N_ChainSync    x (inj₁ (eq , _)) = inj₁ eq
srvRead-adj k kd bfs bfs′ l₀ d₀ N2N_KeepAlive    x (inj₁ (eq , _)) = inj₁ eq
srvRead-adj k kd bfs bfs′ l₀ d₀ N2N_TxSubmission x (inj₁ (eq , _)) = inj₁ eq
srvRead-adj k kd bfs bfs′ l₀ d₀ N2N_LeiosNotify  x (inj₁ (eq , _)) = inj₁ eq
srvRead-adj k kd bfs bfs′ l₀ d₀ N2N_LeiosFetch   x (inj₁ (eq , _)) = inj₁ eq

-- *** (B, cellCp3) THE SAME TWO SELECTORS AT THE CLIENT ROLE. ***  `LIC.CliRowP` is
-- label-directed for exactly the reason `SrvRowP` is, so a consumer at a VARIABLE
-- `IDs` cannot case on it either.  These two are LINK- and KEY-GENERIC and answer at
-- the COARSE position, so both hops can use them.  (The up hop's own consumer —
-- `LiveChanJoin.upFillData` — computes this same fact BESIDE the cell's writer, which
-- is what makes it hop-hardwired; the `cellCp3` down factor wants the client half
-- alone, and that half needs no key dispatch at all: `CliRowP`'s own two arms ARE the
-- answer.)
cliFill-adj : (k : Link) (kd : Dir) (bfc bfc′ : SN.BFcPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
            → LIC.CliRowP k kd bfc bfc′ (input l₀ d₀ id₀) x
            → (coarsenBFc bfc ≡ coarsenBFc bfc′)
              ⊎ CliSendAdj (coarsenBFc bfc) x (coarsenBFc bfc′)
cliFill-adj k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₁ (eq , _)) =
  inj₁ (cong coarsenBFc eq)
cliFill-adj k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₂ (refl , refl , row)) =
  inj₂ (cliSendRow k kd (coarsenBFc bfc) x (coarsenBFc bfc′) row)
cliFill-adj k kd bfc bfc′ l₀ d₀ N2N_ChainSync    x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)
cliFill-adj k kd bfc bfc′ l₀ d₀ N2N_KeepAlive    x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)
cliFill-adj k kd bfc bfc′ l₀ d₀ N2N_TxSubmission x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)
cliFill-adj k kd bfc bfc′ l₀ d₀ N2N_LeiosNotify  x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)
cliFill-adj k kd bfc bfc′ l₀ d₀ N2N_LeiosFetch   x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)

-- … and the READ direction's twin
cliRead-adj : (k : Link) (kd : Dir) (bfc bfc′ : SN.BFcPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
            → LIC.CliRowP k kd bfc bfc′ (output l₀ d₀ id₀) x
            → (coarsenBFc bfc ≡ coarsenBFc bfc′)
              ⊎ CliReadAdj (coarsenBFc bfc) x (coarsenBFc bfc′)
cliRead-adj k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₁ (eq , _)) =
  inj₁ (cong coarsenBFc eq)
cliRead-adj k kd bfc bfc′ l₀ d₀ N2N_BlockFetch   x (inj₂ (refl , refl , row)) =
  inj₂ (cliReadRow k kd (coarsenBFc bfc) x (coarsenBFc bfc′) row)
cliRead-adj k kd bfc bfc′ l₀ d₀ N2N_ChainSync    x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)
cliRead-adj k kd bfc bfc′ l₀ d₀ N2N_KeepAlive    x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)
cliRead-adj k kd bfc bfc′ l₀ d₀ N2N_TxSubmission x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)
cliRead-adj k kd bfc bfc′ l₀ d₀ N2N_LeiosNotify  x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)
cliRead-adj k kd bfc bfc′ l₀ d₀ N2N_LeiosFetch   x (inj₁ (eq , _)) = inj₁ (cong coarsenBFc eq)

-- *** (T7) THE UP-HOP CS CLIENT's io FACT, REDUCED — AND WHY IT NEEDS THIS STEP WHERE
-- THE `pp1`/`pp2` ARMS DID NOT. ***  Grant #11's `LiveLegIoCone.CssRowP` is a BARE `⊎`
-- (its rows are event-generic), so the `pp1` and `pp2` io arms case on it directly.
-- Grant #12's `CscIoRowP` is LABEL-DIRECTED — deliberately, and `LiveLegIoCone:324-343`
-- says why — so at a VARIABLE `IDs` it does not reduce at all.  These two selectors do
-- the channel dispatch ONCE per direction, at an abstract key, exactly as
-- `srvFill-adj`/`srvRead-adj` do it for the BF server; after them the `cp5` chain's io
-- arms are `drvCS-fill-at`'s two lines.
--
-- The fixed arm's OWNERSHIP CERTIFICATE (`NoCliIoAt`) is DROPPED here: the chain's arms
-- refute the fired row outright at `ccIdle`, so they never need to know who wrote the
-- cell.  That certificate is the CS channel invariant's business, not the coupling's.
cscFill-row : (k : Link) (kd : Dir) (csc csc′ : SN.CScPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
            → LIC.CscIoRowP k kd csc csc′ (input l₀ d₀ id₀) x
            → (csc ≡ csc′)
              ⊎ (NS.csCnxt k kd (coarsenCSc csc) (Payload , input l₀ d₀ id₀) x
                 ≡ just (coarsenCSc csc′))
cscFill-row k kd csc csc′ l₀ d₀ N2N_ChainSync    x (inj₁ (eq , _)) = inj₁ eq
cscFill-row k kd csc csc′ l₀ d₀ N2N_ChainSync    x (inj₂ row)      = inj₂ row
cscFill-row k kd csc csc′ l₀ d₀ N2N_BlockFetch   x h = inj₁ h
cscFill-row k kd csc csc′ l₀ d₀ N2N_KeepAlive    x h = inj₁ h
cscFill-row k kd csc csc′ l₀ d₀ N2N_TxSubmission x h = inj₁ h
cscFill-row k kd csc csc′ l₀ d₀ N2N_LeiosNotify  x h = inj₁ h
cscFill-row k kd csc csc′ l₀ d₀ N2N_LeiosFetch   x h = inj₁ h

-- … and the READ direction's twin
cscRead-row : (k : Link) (kd : Dir) (csc csc′ : SN.CScPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
            → LIC.CscIoRowP k kd csc csc′ (output l₀ d₀ id₀) x
            → (csc ≡ csc′)
              ⊎ (NS.csCnxt k kd (coarsenCSc csc) (Payload , output l₀ d₀ id₀) x
                 ≡ just (coarsenCSc csc′))
cscRead-row k kd csc csc′ l₀ d₀ N2N_ChainSync    x (inj₁ (eq , _)) = inj₁ eq
cscRead-row k kd csc csc′ l₀ d₀ N2N_ChainSync    x (inj₂ row)      = inj₂ row
cscRead-row k kd csc csc′ l₀ d₀ N2N_BlockFetch   x h = inj₁ h
cscRead-row k kd csc csc′ l₀ d₀ N2N_KeepAlive    x h = inj₁ h
cscRead-row k kd csc csc′ l₀ d₀ N2N_TxSubmission x h = inj₁ h
cscRead-row k kd csc csc′ l₀ d₀ N2N_LeiosNotify  x h = inj₁ h
cscRead-row k kd csc csc′ l₀ d₀ N2N_LeiosFetch   x h = inj₁ h

------------------------------------------------------------------------
-- §4  THE FIVE STEP CLASSES.  Four frame; only the api class reads a row.
------------------------------------------------------------------------

-- the medium-τ and `break` classes at once: both fix every node record, so the
-- coupling's two components are both fixed and this IS the frame
drvBF-fixed : (l : TwoLegs) (s s′ : SysState)
            → relayOf l s ≡ relayOf l s′
            → dnSrv l s ≡ dnSrv l s′
            -- (T5) … and the CS server's own slot fixity
            → dnCSs l s ≡ dnCSs l s′
            -- (T7) … and the UP-hop CS CLIENT's
            → upCSc l s ≡ upCSc l s′
            → DrvBF l s → DrvBF l s′
drvBF-fixed l s s′ peq seq ceq keq =
  drvBF-frame l s s′ peq (cong coarsenBFs seq) (cong coarsenCSs ceq)
              (cong coarsenCSc keq)

-- the VISIBLE api class — the only one that does work, and all of it is the
-- cone's own `DnSrvDrv`: FRAME when neither the phase nor the server moved, and
-- otherwise the relay's own down-link sync, whose `pp4` LANDING hands over the
-- server's genuine `reqBFRange` row.  Note the second arm does NOT use the
-- coupling at `s` at all: at a `pp4` landing the ROW alone fixes the successor,
-- which is what makes the induction anchor on the entering step.
-- *** (T5) THE `pp1` ARM'S API HALF, AS ONE NAMED STEP. ***  It reads the CS pair
-- ALONE — the BF disjunction says nothing about the CS server, and the two pairs are
-- independent in the types even though the cone always answers them in step.  FRAME
-- when the driver's phase and the CS slot both held; otherwise the cone's LANDING,
-- which is already applied (`LiveLegApiCone` §2b″ read the table at the bundle).
drvCS-api-at : (l : TwoLegs) (s s′ : SysState)
             → LAC.DnCsDrv (dnLink l) (dnCSs l s) (dnCSs l s′) (relayOf l s) (relayOf l s′)
             → DrvBF l s
             → (b : Block₃) → relayOf l s′ ≡ producing b pp1
             → coarsenCSs (dnCSs l s′) ≡ NS.csCanAwait
drvCS-api-at l s s′ (inj₁ (peq , ceq)) db b eq =
  trans (sym (cong coarsenCSs ceq)) (drvCp-to1 l s db b (trans peq eq))
-- (T11c) the landing arm gained a fourth member (the relay's advance); this reader
-- already ended on a wildcard, so it absorbs it
drvCS-api-at l s s′ (inj₂ (land , _)) db b eq = land b eq

-- *** (T6d) THE `pp2` ARM'S API HALF. ***  `drvCS-api-at`'s twin at the REGION, off
-- the SAME cone pair: FRAME when the driver's phase and the CS slot both held (the
-- region is mapped, not transported), and otherwise the pair's SECOND landing, which
-- puts the server at the region's LEFT disjunct.  Like the `pp1` half it reads the CS
-- pair alone, and like it needs no source phase — §2b‴ read the table at the bundle.
drvCS-api-at2 : (l : TwoLegs) (s s′ : SysState)
              → LAC.DnCsDrv (dnLink l) (dnCSs l s) (dnCSs l s′) (relayOf l s) (relayOf l s′)
              → DrvBF l s
              → (b : Block₃) → relayOf l s′ ≡ producing b pp2
              → (coarsenCSs (dnCSs l s′) ≡ NS.csWar)
                ⊎ (coarsenCSs (dnCSs l s′) ≡ NS.csMust)
drvCS-api-at2 l s s′ (inj₁ (peq , ceq)) db b eq =
  csRegion-cong (cong coarsenCSs ceq) (drvCp-to2 l s db b (trans peq eq))
-- (T11b) re-cut by one trailing `_`: `DnCsDrv`'s landing arm is a TRIPLE since the
-- `pp3` landing joined it, and this reader ended on a NON-wildcard.  (T11c) the
-- trailing `_` absorbs the fourth member too, so this line did NOT move again
drvCS-api-at2 l s s′ (inj₂ (_ , aland , _)) db b eq = inj₁ (aland b eq)

-- *** (T7) THE `cp5` CHAIN'S FOUR API HALVES. ***  All four read the SAME cone pair
-- (`LAC.UpCsDrv`) and all four have `drvCS-api-at`'s two-arm shape, but only the FIRST
-- is a landing.  The frame arm is identical in all four — the driver's phase and the
-- client slot both held, so the position transports — and the second arm is where they
-- differ: at `cp2` the cone's LANDING gives the position outright, and at `cp3`/`cp4`/
-- `cp5` the cone gives the SOURCE PHASE plus the client's FIXITY, so the arm reads its
-- own clause one sub-phase back and transports along the fixity.  That self-feeding is
-- `DnSbLand`'s shape (T2), which BOTH landed CS landings were free of.
drvCS-api-c2 : (l : TwoLegs) (s s′ : SysState)
             → LAC.UpCsDrv (upLink l) (upCSc l s) (upCSc l s′) (relayOf l s) (relayOf l s′)
             → DrvBF l s
             → (b : Block₃) → relayOf l s′ ≡ consuming b cp2
             → coarsenCSc (upCSc l s′) ≡ NS.ccIdle
drvCS-api-c2 l s s′ (inj₁ (peq , keq)) db b eq =
  trans (sym (cong coarsenCSc keq)) (drvCp-toC2 l s db b (trans peq eq))
drvCS-api-c2 l s s′ (inj₂ (kland , _ , _ , _)) db b eq = kland b eq

-- … the first CARRYING hop: source `cp2`, and the client held
drvCS-api-c3 : (l : TwoLegs) (s s′ : SysState)
             → LAC.UpCsDrv (upLink l) (upCSc l s) (upCSc l s′) (relayOf l s) (relayOf l s′)
             → DrvBF l s
             → (b : Block₃) → relayOf l s′ ≡ consuming b cp3
             → coarsenCSc (upCSc l s′) ≡ NS.ccIdle
drvCS-api-c3 l s s′ (inj₁ (peq , keq)) db b eq =
  trans (sym (cong coarsenCSc keq)) (drvCp-toC3 l s db b (trans peq eq))
drvCS-api-c3 l s s′ (inj₂ (_ , hop , _ , _)) db b eq =
  let (b′ , peq , keq) = hop b eq
  in  trans (sym (cong coarsenCSc keq)) (drvCp-toC2 l s db b′ peq)

-- … the second, source `cp3`
drvCS-api-c4 : (l : TwoLegs) (s s′ : SysState)
             → LAC.UpCsDrv (upLink l) (upCSc l s) (upCSc l s′) (relayOf l s) (relayOf l s′)
             → DrvBF l s
             → (b : Block₃) → relayOf l s′ ≡ consuming b cp4
             → coarsenCSc (upCSc l s′) ≡ NS.ccIdle
drvCS-api-c4 l s s′ (inj₁ (peq , keq)) db b eq =
  trans (sym (cong coarsenCSc keq)) (drvCp-toC4 l s db b (trans peq eq))
drvCS-api-c4 l s s′ (inj₂ (_ , _ , hop , _)) db b eq =
  let (b′ , peq , keq) = hop b eq
  in  trans (sym (cong coarsenCSc keq)) (drvCp-toC3 l s db b′ peq)

-- … and the third, source `cp4` — the hop that lands the driver at the sub-phase the
-- residual names
drvCS-api-c5 : (l : TwoLegs) (s s′ : SysState)
             → LAC.UpCsDrv (upLink l) (upCSc l s) (upCSc l s′) (relayOf l s) (relayOf l s′)
             → DrvBF l s
             → (b : Block₃) → relayOf l s′ ≡ consuming b cp5
             → coarsenCSc (upCSc l s′) ≡ NS.ccIdle
drvCS-api-c5 l s s′ (inj₁ (peq , keq)) db b eq =
  trans (sym (cong coarsenCSc keq)) (drvCp-toC5 l s db b (trans peq eq))
drvCS-api-c5 l s s′ (inj₂ (_ , _ , _ , hop)) db b eq =
  let (b′ , peq , keq) = hop b eq
  in  trans (sym (cong coarsenCSc keq)) (drvCp-toC4 l s db b′ peq)

drvBF-api : (l : TwoLegs) (s s′ : SysState)
          → LAC.DnSrvDrv l s s′
          → LAC.DnCsDrv (dnLink l) (dnCSs l s) (dnCSs l s′) (relayOf l s) (relayOf l s′)
          -- (T7) … and the leg's UP-hop CS CLIENT pair, the `cp5` chain's own
          → LAC.UpCsDrv (upLink l) (upCSc l s) (upCSc l s′) (relayOf l s) (relayOf l s′)
          → DrvBF l s → DrvBF l s′
drvBF-api l s s′ (inj₁ (peq , seq)) cd ud db =
  drvCp-of l s′ (λ b eq → trans (sym (cong coarsenBFs seq)) (drvCp-to l s db b (trans peq eq)))
                (λ b eq → region-cong (cong coarsenBFs seq)
                            (drvCp-to5 l s db b (trans peq eq)))
                (drvCS-api-at l s s′ cd db)
                (drvCS-api-at2 l s s′ cd db)
                (drvCS-api-c2 l s s′ ud db)
                (drvCS-api-c3 l s s′ ud db)
                (drvCS-api-c4 l s s′ ud db)
                (drvCS-api-c5 l s s′ ud db)
-- (T11h) one more component in the second arm: `DnSrvPre`, which this coupling does
-- not read (its own two landings are what it reads)
drvBF-api l s s′ (inj₂ (land , sland , _)) cd ud db =
  drvCp-of l s′
    (λ b eq →
      let (r , _ , _ , row) = land b eq
      in  srvReqLands (dnLink l) hi (coarsenBFs (dnSrv l s)) r
                      (coarsenBFs (dnSrv l s′)) row)
    -- (T2) the `pp5` landing: the cone reports the SOURCE phase (`pp4`) beside the
    -- server's landing, so the arm feeds itself — the carried `pp4` clause at `s`
    -- is exactly the antecedent the landing wants, and the region's LEFT disjunct
    -- is where the entering step puts the server
    (λ b eq →
      let (b′ , peq , srv) = sland b eq
      in  inj₁ (srv (drvCp-to l s db b′ peq)))
    (drvCS-api-at l s s′ cd db)
    (drvCS-api-at2 l s s′ cd db)
    -- (T7) the `cp5` chain reads its OWN cone pair, independently of the BF
    -- disjunction this clause matched on — the two axes say nothing about each other
    (drvCS-api-c2 l s s′ ud db)
    (drvCS-api-c3 l s s′ ud db)
    (drvCS-api-c4 l s s′ ud db)
    (drvCS-api-c5 l s s′ ud db)

-- the FILL class's own landing, as a NAMED dispatch: either the server was fixed
-- and the position rides across, or its io row fired and `bsBusy` refutes it.
-- (Named, not an inline case-λ: a pattern-matching λ has to have its type given,
-- and inline it leaves the `⊎`'s two sides as unsolved metas — measured,
-- `[UnsolvedMetaVariables]` at exactly the two λs.)
drvBF-fill-at : (l : TwoLegs) (s s′ : SysState) (x : Payload)
              → coarsenBFs (dnSrv l s) ≡ NS.bsBusy
              → (dnSrv l s ≡ dnSrv l s′)
                ⊎ SrvSendAdj (coarsenBFs (dnSrv l s)) x (coarsenBFs (dnSrv l s′))
              → coarsenBFs (dnSrv l s′) ≡ NS.bsBusy
drvBF-fill-at l s s′ x bsy (inj₁ seq) = trans (sym (cong coarsenBFs seq)) bsy
drvBF-fill-at l s s′ x bsy (inj₂ adj) =
  ⊥-elim (srvSend-busy-⊥
           (subst (λ z → SrvSendAdj z x (coarsenBFs (dnSrv l s′))) bsy adj))

-- … the READ twin
drvBF-read-at : (l : TwoLegs) (s s′ : SysState) (x : Payload)
              → coarsenBFs (dnSrv l s) ≡ NS.bsBusy
              → (dnSrv l s ≡ dnSrv l s′)
                ⊎ SrvReadAdj (coarsenBFs (dnSrv l s)) x (coarsenBFs (dnSrv l s′))
              → coarsenBFs (dnSrv l s′) ≡ NS.bsBusy
drvBF-read-at l s s′ x bsy (inj₁ seq) = trans (sym (cong coarsenBFs seq)) bsy
drvBF-read-at l s s′ x bsy (inj₂ adj) =
  ⊥-elim (srvRead-busy-⊥
           (subst (λ z → SrvReadAdj z x (coarsenBFs (dnSrv l s′))) bsy adj))

-- *** (T2) the FILL class at the `pp5` REGION. ***  Three cases, not two: the server
-- rides (frame), or its row fired at `bsWsb` and CLOSES into `bsStream`, or it fired
-- at `bsStream` and is refuted.  (Named for `drvBF-fill-at`'s measured reason.)
--
-- *** REUSE CAVEAT (review M-5). ***  This helper, its READ twin and `region-cong` are
-- HARD-WIRED to `{bsWsb, bsStream}` — the disjunction is written out, not abstracted.
-- T8's `cp4` region is a THREE-element CLIENT region and is NOT io-closed, so those
-- arms will be BUILT, not instantiated from these three; what does transpose to `cp4`
-- is `LiveSrvOpen.srvSendMove-at-⊥` (payload-generic) and the tag-pin kit
-- (`LiveLegApiCone` §1c′).  Do not price `cp4` as a re-instantiation of this section.
drvBF-fill-at5 : (l : TwoLegs) (s s′ : SysState) (x : Payload)
               → (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
                 ⊎ (coarsenBFs (dnSrv l s) ≡ NS.bsStream)
               → (dnSrv l s ≡ dnSrv l s′)
                 ⊎ SrvSendAdj (coarsenBFs (dnSrv l s)) x (coarsenBFs (dnSrv l s′))
               → (coarsenBFs (dnSrv l s′) ≡ NS.bsWsb)
                 ⊎ (coarsenBFs (dnSrv l s′) ≡ NS.bsStream)
drvBF-fill-at5 l s s′ x rg (inj₁ seq) = region-cong (cong coarsenBFs seq) rg
drvBF-fill-at5 l s s′ x (inj₁ w) (inj₂ adj) =
  inj₂ (srvSend-wsb-stream
         (subst (λ z → SrvSendAdj z x (coarsenBFs (dnSrv l s′))) w adj))
drvBF-fill-at5 l s s′ x (inj₂ st) (inj₂ adj) =
  ⊥-elim (srvSend-stream-⊥
           (subst (λ z → SrvSendAdj z x (coarsenBFs (dnSrv l s′))) st adj))

-- … the READ twin, where BOTH disjuncts refute the fired-row arm
drvBF-read-at5 : (l : TwoLegs) (s s′ : SysState) (x : Payload)
               → (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
                 ⊎ (coarsenBFs (dnSrv l s) ≡ NS.bsStream)
               → (dnSrv l s ≡ dnSrv l s′)
                 ⊎ SrvReadAdj (coarsenBFs (dnSrv l s)) x (coarsenBFs (dnSrv l s′))
               → (coarsenBFs (dnSrv l s′) ≡ NS.bsWsb)
                 ⊎ (coarsenBFs (dnSrv l s′) ≡ NS.bsStream)
drvBF-read-at5 l s s′ x rg (inj₁ seq) = region-cong (cong coarsenBFs seq) rg
drvBF-read-at5 l s s′ x (inj₁ w) (inj₂ adj) =
  ⊥-elim (srvRead-wsb-⊥
           (subst (λ z → SrvReadAdj z x (coarsenBFs (dnSrv l s′))) w adj))
drvBF-read-at5 l s s′ x (inj₂ st) (inj₂ adj) =
  ⊥-elim (srvRead-stream-⊥
           (subst (λ z → SrvReadAdj z x (coarsenBFs (dnSrv l s′))) st adj))

-- *** (T5) THE io CLASSES AT THE `pp1` ARM. ***  `csCanAwait` is io-CLOSED, so both
-- directions are the `bsBusy` case and not the `bsWsb` one: the peer rides across
-- when it did not move, and its fired ROW is refuted outright by `LiveCSRow` §4b's
-- two generic refutations.  No adjacency datatype is involved — grant #11's fact
-- carries the coarse ROW itself, so the refutation is one `subst`.
drvCS-fill-at : (l : TwoLegs) (s s′ : SysState)
                (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
              → coarsenCSs (dnCSs l s) ≡ NS.csCanAwait
              → LIC.CssRowP (dnLink l) hi (dnCSs l s) (dnCSs l s′) (input l₀ d₀ id₀) x
              → coarsenCSs (dnCSs l s′) ≡ NS.csCanAwait
drvCS-fill-at l s s′ l₀ d₀ id₀ x aw (inj₁ ceq) = trans (sym (cong coarsenCSs ceq)) aw
drvCS-fill-at l s s′ l₀ d₀ id₀ x aw (inj₂ row) =
  ⊥-elim (cssCanAwait-in-⊥ (dnLink l) hi l₀ d₀ id₀ x (coarsenCSs (dnCSs l s′))
           (subst (λ z → NS.csSnxt (dnLink l) hi z (Payload , input l₀ d₀ id₀) x
                         ≡ just (coarsenCSs (dnCSs l s′)))
                  aw row))

-- … the READ twin
drvCS-read-at : (l : TwoLegs) (s s′ : SysState)
                (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
              → coarsenCSs (dnCSs l s) ≡ NS.csCanAwait
              → LIC.CssRowP (dnLink l) hi (dnCSs l s) (dnCSs l s′) (output l₀ d₀ id₀) x
              → coarsenCSs (dnCSs l s′) ≡ NS.csCanAwait
drvCS-read-at l s s′ l₀ d₀ id₀ x aw (inj₁ ceq) = trans (sym (cong coarsenCSs ceq)) aw
drvCS-read-at l s s′ l₀ d₀ id₀ x aw (inj₂ row) =
  ⊥-elim (cssCanAwait-out-⊥ (dnLink l) hi l₀ d₀ id₀ x (coarsenCSs (dnCSs l s′))
           (subst (λ z → NS.csSnxt (dnLink l) hi z (Payload , output l₀ d₀ id₀) x
                         ≡ just (coarsenCSs (dnCSs l s′)))
                  aw row))

-- *** (T6d) THE io CLASSES AT THE `pp2` REGION. ***  Unlike `csCanAwait`, `csWar` is
-- NOT io-closed on its own — its ONE io row is the server's own `MsgCSAwaitReply`
-- wire-send — but the REGION is io-closed: that row lands at `csMust` (`LiveCSRow`
-- §4c's `cssWar-in-must`, which has to dispatch on the `IDs`), `csWar` has no io READ
-- row (`cssWar-out-⊥`) and `csMust` refutes BOTH directions (`cssMust-in-⊥`/
-- `cssMust-out-⊥`).  So the FILL direction is `drvBF-fill-at5`'s three-case shape and
-- the READ direction is `drvBF-read-at5`'s: one arm carries, the rest refute.
drvCS-fill-at2 : (l : TwoLegs) (s s′ : SysState)
                 (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               → (coarsenCSs (dnCSs l s) ≡ NS.csWar)
                 ⊎ (coarsenCSs (dnCSs l s) ≡ NS.csMust)
               → LIC.CssRowP (dnLink l) hi (dnCSs l s) (dnCSs l s′) (input l₀ d₀ id₀) x
               → (coarsenCSs (dnCSs l s′) ≡ NS.csWar)
                 ⊎ (coarsenCSs (dnCSs l s′) ≡ NS.csMust)
drvCS-fill-at2 l s s′ l₀ d₀ id₀ x rg (inj₁ ceq) =
  csRegion-cong (cong coarsenCSs ceq) rg
drvCS-fill-at2 l s s′ l₀ d₀ id₀ x (inj₁ war) (inj₂ row) =
  inj₂ (cssWar-in-must (dnLink l) hi l₀ d₀ id₀ x (coarsenCSs (dnCSs l s′))
         (subst (λ z → NS.csSnxt (dnLink l) hi z (Payload , input l₀ d₀ id₀) x
                       ≡ just (coarsenCSs (dnCSs l s′)))
                war row))
drvCS-fill-at2 l s s′ l₀ d₀ id₀ x (inj₂ must) (inj₂ row) =
  ⊥-elim (cssMust-in-⊥ (dnLink l) hi l₀ d₀ id₀ x (coarsenCSs (dnCSs l s′))
           (subst (λ z → NS.csSnxt (dnLink l) hi z (Payload , input l₀ d₀ id₀) x
                         ≡ just (coarsenCSs (dnCSs l s′)))
                  must row))

-- … the READ twin, where BOTH ends of the region refute the fired-row arm
drvCS-read-at2 : (l : TwoLegs) (s s′ : SysState)
                 (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               → (coarsenCSs (dnCSs l s) ≡ NS.csWar)
                 ⊎ (coarsenCSs (dnCSs l s) ≡ NS.csMust)
               → LIC.CssRowP (dnLink l) hi (dnCSs l s) (dnCSs l s′) (output l₀ d₀ id₀) x
               → (coarsenCSs (dnCSs l s′) ≡ NS.csWar)
                 ⊎ (coarsenCSs (dnCSs l s′) ≡ NS.csMust)
drvCS-read-at2 l s s′ l₀ d₀ id₀ x rg (inj₁ ceq) =
  csRegion-cong (cong coarsenCSs ceq) rg
drvCS-read-at2 l s s′ l₀ d₀ id₀ x (inj₁ war) (inj₂ row) =
  ⊥-elim (cssWar-out-⊥ (dnLink l) hi l₀ d₀ id₀ x (coarsenCSs (dnCSs l s′))
           (subst (λ z → NS.csSnxt (dnLink l) hi z (Payload , output l₀ d₀ id₀) x
                         ≡ just (coarsenCSs (dnCSs l s′)))
                  war row))
drvCS-read-at2 l s s′ l₀ d₀ id₀ x (inj₂ must) (inj₂ row) =
  ⊥-elim (cssMust-out-⊥ (dnLink l) hi l₀ d₀ id₀ x (coarsenCSs (dnCSs l s′))
           (subst (λ z → NS.csSnxt (dnLink l) hi z (Payload , output l₀ d₀ id₀) x
                         ≡ just (coarsenCSs (dnCSs l s′)))
                  must row))

-- *** (T7) THE io CLASSES AT THE `cp5` CHAIN. ***  `ccIdle` is io-CLOSED — its three
-- rows are all `apiCS` (`NodeSpecs:306-314`) — so both directions are `csCanAwait`'s
-- case and not `csWar`'s: the client rides across when it did not move, and its fired
-- ROW is refuted outright by `LiveCSRow` §4b's two generic refutations.  ONE arm serves
-- all four sub-phases, because all four state the SAME equation: the source phase plays
-- no part in an io step (the driver's phase is FIXED across one), which is why this
-- section is two lemmas and not eight.
drvCS-fill-atC : (l : TwoLegs) (s s′ : SysState)
                 (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               → coarsenCSc (upCSc l s) ≡ NS.ccIdle
               → (upCSc l s ≡ upCSc l s′)
                 ⊎ (NS.csCnxt (upLink l) hi (coarsenCSc (upCSc l s))
                      (Payload , input l₀ d₀ id₀) x ≡ just (coarsenCSc (upCSc l s′)))
               → coarsenCSc (upCSc l s′) ≡ NS.ccIdle
drvCS-fill-atC l s s′ l₀ d₀ id₀ x idl (inj₁ keq) = trans (sym (cong coarsenCSc keq)) idl
drvCS-fill-atC l s s′ l₀ d₀ id₀ x idl (inj₂ row) =
  ⊥-elim (cscIdle-in-⊥ (upLink l) hi l₀ d₀ id₀ x (coarsenCSc (upCSc l s′))
           (subst (λ z → NS.csCnxt (upLink l) hi z (Payload , input l₀ d₀ id₀) x
                         ≡ just (coarsenCSc (upCSc l s′)))
                  idl row))

-- … the READ twin
drvCS-read-atC : (l : TwoLegs) (s s′ : SysState)
                 (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               → coarsenCSc (upCSc l s) ≡ NS.ccIdle
               → (upCSc l s ≡ upCSc l s′)
                 ⊎ (NS.csCnxt (upLink l) hi (coarsenCSc (upCSc l s))
                      (Payload , output l₀ d₀ id₀) x ≡ just (coarsenCSc (upCSc l s′)))
               → coarsenCSc (upCSc l s′) ≡ NS.ccIdle
drvCS-read-atC l s s′ l₀ d₀ id₀ x idl (inj₁ keq) = trans (sym (cong coarsenCSc keq)) idl
drvCS-read-atC l s s′ l₀ d₀ id₀ x idl (inj₂ row) =
  ⊥-elim (cscIdle-out-⊥ (upLink l) hi l₀ d₀ id₀ x (coarsenCSc (upCSc l s′))
           (subst (λ z → NS.csCnxt (upLink l) hi z (Payload , output l₀ d₀ id₀) x
                         ≡ just (coarsenCSc (upCSc l s′)))
                  idl row))

-- the io FILL class — the coupling frames, and the fired-row arm is REFUTED at
-- `bsBusy` (no `SrvSendAdj` leaves it)
drvBF-fill : (l : TwoLegs) (s s′ : SysState)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
           → relayOf l s ≡ relayOf l s′
           → LIC.SrvRowP (dnLink l) hi (dnSrv l s) (dnSrv l s′) (input l₀ d₀ id₀) x
           -- (T5, grant #11) … and the leg's down-hop CS SERVER's own fact
           → LIC.CssRowP (dnLink l) hi (dnCSs l s) (dnCSs l s′) (input l₀ d₀ id₀) x
           -- (T7, grant #12) … and the leg's UP-hop CS CLIENT's, label-directed
           → LIC.CscIoRowP (upLink l) hi (upCSc l s) (upCSc l s′) (input l₀ d₀ id₀) x
           → DrvBF l s → DrvBF l s′
drvBF-fill l s s′ l₀ d₀ id₀ x peq srvP cssP cscP db =
  drvCp-of l s′
    (λ b eq →
      drvBF-fill-at l s s′ x (drvCp-to l s db b (trans peq eq))
        (srvFill-adj (dnLink l) hi (dnSrv l s) (dnSrv l s′) l₀ d₀ id₀ x srvP))
    (λ b eq →
      drvBF-fill-at5 l s s′ x (drvCp-to5 l s db b (trans peq eq))
        (srvFill-adj (dnLink l) hi (dnSrv l s) (dnSrv l s′) l₀ d₀ id₀ x srvP))
    (λ b eq →
      drvCS-fill-at l s s′ l₀ d₀ id₀ x (drvCp-to1 l s db b (trans peq eq)) cssP)
    -- (T6d) … and the `pp2` REGION at the same fact
    (λ b eq →
      drvCS-fill-at2 l s s′ l₀ d₀ id₀ x (drvCp-to2 l s db b (trans peq eq)) cssP)
    -- (T7) … and the chain's four arms at the CLIENT's fact, reduced once per arm
    (λ b eq →
      drvCS-fill-atC l s s′ l₀ d₀ id₀ x (drvCp-toC2 l s db b (trans peq eq))
        (cscFill-row (upLink l) hi (upCSc l s) (upCSc l s′) l₀ d₀ id₀ x cscP))
    (λ b eq →
      drvCS-fill-atC l s s′ l₀ d₀ id₀ x (drvCp-toC3 l s db b (trans peq eq))
        (cscFill-row (upLink l) hi (upCSc l s) (upCSc l s′) l₀ d₀ id₀ x cscP))
    (λ b eq →
      drvCS-fill-atC l s s′ l₀ d₀ id₀ x (drvCp-toC4 l s db b (trans peq eq))
        (cscFill-row (upLink l) hi (upCSc l s) (upCSc l s′) l₀ d₀ id₀ x cscP))
    (λ b eq →
      drvCS-fill-atC l s s′ l₀ d₀ id₀ x (drvCp-toC5 l s db b (trans peq eq))
        (cscFill-row (upLink l) hi (upCSc l s) (upCSc l s′) l₀ d₀ id₀ x cscP))

-- … and the io READ class, the same at the other direction
drvBF-read : (l : TwoLegs) (s s′ : SysState)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
           → relayOf l s ≡ relayOf l s′
           → LIC.SrvRowP (dnLink l) hi (dnSrv l s) (dnSrv l s′) (output l₀ d₀ id₀) x
           -- (T5, grant #11) … the READ direction's twin
           → LIC.CssRowP (dnLink l) hi (dnCSs l s) (dnCSs l s′) (output l₀ d₀ id₀) x
           -- (T7, grant #12) … and the up-hop CLIENT's
           → LIC.CscIoRowP (upLink l) hi (upCSc l s) (upCSc l s′) (output l₀ d₀ id₀) x
           → DrvBF l s → DrvBF l s′
drvBF-read l s s′ l₀ d₀ id₀ x peq srvP cssP cscP db =
  drvCp-of l s′
    (λ b eq →
      drvBF-read-at l s s′ x (drvCp-to l s db b (trans peq eq))
        (srvRead-adj (dnLink l) hi (dnSrv l s) (dnSrv l s′) l₀ d₀ id₀ x srvP))
    (λ b eq →
      drvBF-read-at5 l s s′ x (drvCp-to5 l s db b (trans peq eq))
        (srvRead-adj (dnLink l) hi (dnSrv l s) (dnSrv l s′) l₀ d₀ id₀ x srvP))
    (λ b eq →
      drvCS-read-at l s s′ l₀ d₀ id₀ x (drvCp-to1 l s db b (trans peq eq)) cssP)
    -- (T6d) … and the READ direction's `pp2` twin
    (λ b eq →
      drvCS-read-at2 l s s′ l₀ d₀ id₀ x (drvCp-to2 l s db b (trans peq eq)) cssP)
    -- (T7) … and the chain's four arms
    (λ b eq →
      drvCS-read-atC l s s′ l₀ d₀ id₀ x (drvCp-toC2 l s db b (trans peq eq))
        (cscRead-row (upLink l) hi (upCSc l s) (upCSc l s′) l₀ d₀ id₀ x cscP))
    (λ b eq →
      drvCS-read-atC l s s′ l₀ d₀ id₀ x (drvCp-toC3 l s db b (trans peq eq))
        (cscRead-row (upLink l) hi (upCSc l s) (upCSc l s′) l₀ d₀ id₀ x cscP))
    (λ b eq →
      drvCS-read-atC l s s′ l₀ d₀ id₀ x (drvCp-toC4 l s db b (trans peq eq))
        (cscRead-row (upLink l) hi (upCSc l s) (upCSc l s′) l₀ d₀ id₀ x cscP))
    (λ b eq →
      drvCS-read-atC l s s′ l₀ d₀ id₀ x (drvCp-toC5 l s db b (trans peq eq))
        (cscRead-row (upLink l) hi (upCSc l s) (upCSc l s′) l₀ d₀ id₀ x cscP))

------------------------------------------------------------------------
-- §5  THE DISCHARGED ARM, AT THE RESIDUAL'S OWN SHAPE.
--
-- The coupling's field IS `LiveRelayCS.BFAt`'s `pp4` clause, but that clause is
-- stated at the driver's ACTUAL phase, so the consumer needs the equation at an
-- EXPLICIT phase argument plus the reflexivity that ties it to `relayOf l s`.
-- That is this lemma, and it is what `LiveRelayCS` §3 applies at `pp4`.
------------------------------------------------------------------------

-- the `pp4` equation, off the coupling, at an explicit phase
drvBF-at-pp4 : (l : TwoLegs) (s : SysState) (b : Block₃)
             → relayOf l s ≡ producing b pp4
             → DrvBF l s → coarsenBFs (dnSrv l s) ≡ NS.bsBusy
drvBF-at-pp4 l s b eq db = drvCp-to l s db b eq

-- … and the `pp5` REGION, at an explicit phase.  The consumer sharpens it to the
-- residual's own equation with the stability refutation of `bsWsb`
-- (`LiveSrvOpen.srvWsb-⊥`) — see `LiveRelayCS` §3.
drvBF-at-pp5 : (l : TwoLegs) (s : SysState) (b : Block₃)
             → relayOf l s ≡ producing b pp5
             → DrvBF l s
             → (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
               ⊎ (coarsenBFs (dnSrv l s) ≡ NS.bsStream)
drvBF-at-pp5 l s b eq db = drvCp-to5 l s db b eq

-- … and (T5) the `pp1` equation, at an explicit phase.  Unlike `pp5`'s this needs no
-- sharpening at the consumer: `csCanAwait` is a POSITION the coupling carries
-- outright, because the one row into it lands there (`LiveCSRow.cssReqLands`).
drvCS-at-pp1 : (l : TwoLegs) (s : SysState) (b : Block₃)
             → relayOf l s ≡ producing b pp1
             → DrvBF l s → coarsenCSs (dnCSs l s) ≡ NS.csCanAwait
drvCS-at-pp1 l s b eq db = drvCp-to1 l s db b eq

-- … and the (T6d) `pp2` REGION, at an explicit phase.  The consumer sharpens it to
-- the residual's own equation with the stability refutation of `csWar`
-- (`LiveSrvOpen.csWar-⊥`) — see `LiveRelayCS` §3, exactly as `pp5`'s is sharpened
drvCS-at-pp2 : (l : TwoLegs) (s : SysState) (b : Block₃)
             → relayOf l s ≡ producing b pp2
             → DrvBF l s
             → (coarsenCSs (dnCSs l s) ≡ NS.csWar)
               ⊎ (coarsenCSs (dnCSs l s) ≡ NS.csMust)
drvCS-at-pp2 l s b eq db = drvCp-to2 l s db b eq

-- … and (T7) the `cp5` POSITION, at an explicit phase.  Like `pp1`'s and unlike
-- `pp2`/`pp5`'s this needs NO sharpening at the consumer: the one row into `ccIdle`
-- lands there (`LiveCSRow.cscRfwLands`), so the coupling carries the residual's own
-- equation outright and `LiveRelayCS.coAt-split-at`'s `cp5` clause is one application.
-- The chain's other three clauses have NO accessor here on purpose — they are carriers
-- with no consumer outside this module, and exporting them would invite a reader to
-- mistake a carrier for a discharged arm.
drvCS-at-cp5 : (l : TwoLegs) (s : SysState) (b : Block₃)
             → relayOf l s ≡ consuming b cp5
             → DrvBF l s → coarsenCSc (upCSc l s) ≡ NS.ccIdle
drvCS-at-cp5 l s b eq db = drvCp-toC5 l s db b eq

------------------------------------------------------------------------
-- §6  FALSIFICATIONS — four from (T1), one per NOVEL arm family, (T2)'s three and
-- (T6d)'s one:
-- F17 on the Π-bridge the shape switch introduced and F19/F20 on the two novel arm
-- families of the `pp5` region.  All arity-preserving, all RED, all reverted
-- byte-identically (`git diff --stat HEAD` verified back to the intended diff after
-- each batch).  (F12 and F18, the two discharges themselves, are recorded at their
-- own site — `LiveRelayCS` §7; F21, the sharpening's ladder, at `LiveSrvOpen` §3.)
--
-- (F13  THE OWN-KEY ROW IS DIRECTED)  `LiveLegApiCone`'s `bfEvRio→api` feeds
--      `srvReqRow-of` its two peer positions SWAPPED (`bfs′ bfs` for `bfs bfs′`) —
--      same arity, both in scope.
--      *** RED ***: `LiveLegApiCone:1017.39-42: [UnequalTerms] bfs != bfs′ of type
--      BFsPos … when checking that the expression row has type SrvApiRow l sv l′ d′
--      bfs′ bfs m _a`, EXIT=42.  So the new bundle slot really is the
--      PREDECESSOR-to-SUCCESSOR row and not a symmetric relation: S1's api arm reads
--      the landing off it in one direction only.
--
-- (F14  THE LABEL PIN IS AT THE PRODUCE LINK)  `cpStepKindQ-of⁺`'s tenth component
--      calls `prod-a34-anchor` at the CONSUME link `l₁` instead of the produce link
--      `l₂` — same arity, both in scope (they are the classifier's own two
--      parameters).
--      *** RED ***: `LiveLegApiCone:1540.41-1542.89: [UnequalTerms] l₂ != l₁ of type
--      Fin (Params.numLinks p) … the inferred type of an application decProd l₂ hi b
--      pp3 ─[ … ]─► _ matches the expected type decProd l₁ hi b pp3 ─[ … ]─► _`,
--      EXIT=42.  So the pin is pinned to the leg's DOWN key, which is what makes the
--      up-link-fired arm of the node peels refutable and the down-link-fired arm
--      usable.
--
-- (F15  THE TWO LEGS' CONE SLOTS ARE NOT INTERCHANGEABLE)  `driverExpose⁺`'s
--      node-B-fired arm returns its two `DnSrvDrv` slots in the opposite order
--      (`inj₁ (refl , refl) , inj₂ dnReqB`) — same arity, same constructors.
--      *** RED *** (anchor ERA-SCOPED to T1: T3b's record conversion re-numbered the
--      file and its split moved this site to `LiveLegApiExpose`):
--      `LiveLegApiCone:2528.15-19: [UnequalTerms] SN.cp-B (nB s) !=
--      SN.cp-B nb′ of type CPPh … when checking that the expression refl has type
--      SN.cp-B (nB s) ≡ SN.cp-B nb′`, EXIT=42 — i.e. the FRAME arm is false of the
--      leg whose relay node fired, exactly as the disjunction's design says.
--
-- (F16  THE io REFUTATION RUNS ON THE PREDECESSOR)  `drvBF-fill-at` substitutes the
--      coupling's `bsBusy` into the adjacency's TARGET instead of its SOURCE
--      (`subst (λ z → SrvSendAdj (coarsenBFs (dnSrv l s)) x z)`) — same arity, same
--      witness.
--      *** RED ***: `:266.13-74: [UnequalTerms] coarsenBFs (dnSrv l s) != NS.bsBusy
--      of type NS.BFsPos … the inferred type of an application SrvSendAdj
--      (coarsenBFs (dnSrv l s)) x _y matches the expected type SrvSendAdj NS.bsBusy
--      _x _q`, EXIT=42.  So the io arms are closed by "no io row LEAVES `bsBusy`",
--      which is a fact about the position the INVARIANT names — not about wherever
--      the step happened to land.
--
-- (F17  (T2) THE Π-BRIDGE IS INDEXED BY THE PHASE THAT FIRES THE ARM)  `drvCp-to`
--      instantiates the carried Π at `producing b pp3` instead of `producing b pp4`
--      — same arity, both in scope, and `pp3` is the neighbouring FUNDED arm of the
--      residual (`BFAt`'s `Σ[ rg ] … ≡ bsAreq rg`), so this is the mutation a
--      re-indexing typo would actually make.
--      *** RED ***: `:200.43-45: [UnequalTerms] pp4 != pp3 of type SN.ProdPh … when
--      checking that the expression eq has type relayOf l s ≡ producing b pp3`,
--      EXIT=42.  So the bridge cannot be pointed at a different
--      sub-phase and still typecheck: the carried coupling delivers `DrvCp` at
--      EXACTLY the shape the equation names, which is what makes §1's clause list
--      and `LiveRelayCS.BFAt`'s the same list.
--
-- (F19  (T2) THE ENTERING STEP LANDS IN THE REGION'S *LEFT* DISJUNCT)  the api arm's
--      `pp5` half returns `inj₂ (srv …)` instead of `inj₁ (srv …)` — same arity, same
--      witness, and `inj₂` is the disjunct the arm is ultimately AFTER, so this is the
--      optimistic mutation an author would actually write.
--      *** RED ***: `:412.17-44: [UnequalTerms] NS.bsWsb != NS.bsStream of type
--      NS.BFsPos … the inferred type of an application coarsenBFs (dnSrv l s′) ≡
--      NS.bsWsb matches the expected type coarsenBFs (dnSrv l s′) ≡ NS.bsStream`,
--      EXIT=42.  So the region is not decoration: at the step that ENTERS `pp5` the
--      server is provably at `bsWsb` and provably NOT at `bsStream`, which is exactly
--      why the residual's singleton equation needs the stability half.
--
-- (F20  (T2) THE CLOSING ROW MOVES THE SERVER ON)  `drvBF-fill-at5`'s fired-row arm
--      at `bsWsb` returns `inj₁` instead of `inj₂` — same arity, same witness — i.e.
--      it claims the wire-send leaves the server where it was.
--      *** RED ***: `:452.9-453.71: [UnequalTerms] NS.bsStream != NS.bsWsb of type
--      NS.BFsPos …`, EXIT=42.  So `ssSB`'s target is read off the row and not assumed:
--      the region is closed BECAUSE the one io row inside it lands at its other end.
--
-- *** AND THE GUARD (T2) PUT BACK. ***  T1's record of implications gave up the
-- property that a new `ProdPh` constructor is a type error HERE (`LiveRelayCS`'s
-- F7/F8 property for `CSAt`/`BFAt`).  §1's total dispatch RESTORES it, at two sites:
-- `DrvCp`'s seventeen clauses and `drvCp-of`'s seventeen, the second of which is the
-- one that forces the DISCHARGE-or-PREMISE decision — a new funded arm has to arrive
-- there as a new argument, so it cannot be defaulted to `⊤` by silence.  F12 is NOT
-- made redundant by that and is deliberately kept: it tests a DIFFERENT claim (that
-- `BFAt`'s `⊤` at `pp4` is not a silent weakening — `CoAt`'s own clause still demands
-- the equation and nothing but the coupling supplies it), and no coverage check can
-- see that.  The two guards are orthogonal: F12 guards the CONTENT of a discharged
-- arm, totality guards the EXISTENCE of an arm per sub-phase.
--
-- (F42  (T6d) THE CS REGION'S CLOSING ROW MOVES THE SERVER ON)  `drvCS-fill-at2`'s
--      fired-row arm at `csWar` returns `inj₁` instead of `inj₂` — same arity, same
--      witness — i.e. it claims the server's own `MsgCSAwaitReply` wire-send leaves it
--      where it was.  F20's mutation one axis over.
--      *** RED ***: `:688.9-691.24: [UnequalTerms] NS.csMust != NS.csWar of type
--      NS.CSsPos …`, EXIT=42.  So `cssWar-in-must`'s target is READ OFF the row and
--      not assumed: the `pp2` region is closed BECAUSE the one io row inside it lands
--      at its other end, and `csWar` alone would be FALSE at the next state.  (The
--      other two arms of the region are refutations, so no mutation of theirs is
--      non-vacuous; the region's ENTRY is guarded by F41 at `LiveLegApiCone` and its
--      DISCHARGE by F43 at `LiveRelayCS` §7.)
--
-- (F45  (T7) A CARRYING HOP READS ITS OWN CLAUSE ONE SUB-PHASE BACK, NOT AT ITS OWN)
--      `drvCS-api-c3`'s landing arm instantiates the carried Π at `drvCp-toC3` instead of
--      `drvCp-toC2` — same arity, both in scope, and the mutation an author would make
--      first, because the arm's CONCLUSION is at `cp3` and reaching for the `cp3` bridge
--      reads as the natural move.  This is the falsification of the `cp5` chain's second
--      NOVEL arm family (F44 guards the first, the LANDING).
--      *** RED ***: `:744.63-66: [UnequalTerms] cp2 != cp3 of type SN.ConsPh … when
--      checking that the expression peq has type relayOf l s ≡ consuming b′ cp3`,
--      EXIT=42.  So the SOURCE PHASE the cone reports is load-bearing and the induction
--      really does step: the arm cannot prove `ccIdle` at `s′` from `ccIdle` at `s` by
--      pointing at its own sub-phase, which would be circular, and the type system says
--      so at the bridge rather than anywhere downstream.  The same mutation at
--      `drvCS-api-c4`/`-c5` is the identical shape one hop on and is not run separately.
--      (F17 is this mutation's PRODUCE-side ancestor: the Π-bridge cannot be pointed at a
--      different sub-phase and still typecheck.)
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `LiveStableOffer` — the `stabR` CORE of the four-node block-liveness
-- failure simulation: at every reachable STABLE state of the hidden
-- abstraction whose decode says `pᵢ ∧ gᵢ`, the kept receive
-- `apiBF link{BD,CD} hi recvBFBlock · blkA` is OFFERED.
--
-- THE OBLIGATION, verbatim (`Semantics/BisimFromRel.agda:103-107`, the `stabR`
-- parameter of `FSimFromRel`):
--
--   stabR : ∀ {p q} → Rel p q → isStable p
--         → Σ[ q′ ] ((q ─[τ*]─► q′) × isStable q′
--                    × (∀ e → Offers q′ e → Offers p e))
--
-- with `p := radec r ∖ hidden blkA` (the implementation: the ABSTRACT decode
-- `absDec (toSys r)` under the hide) and `q := SpecOf r` (the CSP spec state the
-- coupling names).  `Settle` below is that Σ-type; `StabOffer r` is the whole
-- obligation at one reachable config.
--
-- ---------------------------------------------------------------------
-- WHAT THIS MODULE DELIVERS (slices 1-4), AND WHAT IT DOES NOT.
--
-- THE HEADLINE, in one line: `stabR` holds at every reachable config, from the
-- CARRIED joint invariant plus SIX open in-flight positions — `stabR-final`
-- (§11).  The spec side (§3), the dispatch (§4), the whole OFFER half (§5-§7),
-- the block pin (§9) and the progress half's machinery + its `lpUpClient` arm
-- (§10-§11) are done; what is left is the six-field `InFlightOpen`, and §11's
-- header says exactly what each field needs and why it is not buildable here.
--
-- READING ORDER for the residual: §11's block comment is the authoritative
-- statement of the R3′ finding (two families, different missing ingredients);
-- the "WHAT PACKAGE (3) MUST HIT" block below is kept only as the record of the
-- interface it was briefed against, and is now DISCHARGED by §11.
--
-- DELIVERED, unconditionally:
--   §3  the SPEC SIDE, complete: the τ*-settled branch, its stability and its
--       offer set, for all THREE `SpecPos` classes.  `posIdle` and `posDone`
--       settle on `Stop` (`idleτ`/`Done`'s branch 0), which is stable and
--       offers NOTHING, so their containment is vacuous and those two arms of
--       `stabR` are DISCHARGED OUTRIGHT — no implementation fact whatsoever.
--       `posProd` settles on branch 0, `ptree (react (delivMenu …) ∅t)`, whose
--       offer set is exactly `delivMenu blkA p1 g1 p2 g2`.
--   §4  the DISPATCH: `stabOffer` reduces the whole obligation to ONE residual
--       premise, `DelivObl`, demanded only at `posProd` — "whatever branch 0's
--       menu offers, the implementation offers".  This is the exact interface
--       the rest of the campaign has to fill, and it is stated over the menu
--       rather than over two hand-written events so that no event-set
--       bookkeeping is duplicated.
--   §2  the OBLIGATED-WINDOW READER (`window-BD`/`window-CD`): from the spec
--       position `posProd q1 q2 q3 q4` with that leg's two flags `true`, the
--       leg's component facts `ProdSent (prodOf l s)`, `InCp03 (phOf l s)` and
--       the unbrokenness of the leg's TWO links — i.e. exactly `legInv⇒token`'s
--       premise set (`window⇒token` composes it), plus what an io-class enabled
--       move needs (a broken link's medium is `Skip` and offers nothing).
--   §5  the PARKED OFFER, piece by piece: the BF client's own offer of
--       `recvBFBlock · b` at `bcBlk1 b`, its lift through the 12-peer bundle,
--       D's consume driver's offer at `cp3`, the node-D api fingerprint, and the
--       "not hidden" side condition of the kept receive.
--   §6  the LADDER: node D's driver↔peer SYNC, the three sibling-node solo
--       lifts, the io-gate solo past the medium, and BOTH hides — ending in
--       `parkedOffer-BD`/`parkedOffer-CD`, "`AtPos leg lpDnClient blkA` makes the
--       kept receive an OFFER of `radec r ∖ hidden blkA`".
--   §7  the MENU TRANSPORT (`outputHit`) and THE DISCHARGE: `delivObl-parked`
--       proves the residual `DelivObl` of §4 from the two parked positions, and
--       `stabOffer-parked` composes it with §4's dispatch into the whole `stabR`
--       obligation.  The two premises are PER-LEG and each is CONDITIONAL on
--       that leg's own gate (`pᵢ ∧ gᵢ ≡ true`), because `delivMenu` asks for a
--       leg's receive only when that leg is obligated.
--   §10 THE PROGRESS HALF'S MACHINERY, and its first arm: `hiddenMove-⊥` (the
--       three-level hide arithmetic — a HIDDEN visible move of `radec r` is a τ
--       of `radec r ∖ hidden blkA`, which `stable-no-τ` refutes; this is the ONLY
--       consumer of the threaded `isStable` witness), `apiNodes-whole` (the
--       api-class whole-system lift, generic in the event), the relay driver's
--       `cp3` offer through its OWN bind continuation, the two relay nodes'
--       driver↔peer SYNCS, the four-node lifts at operands 2 and 3, and
--       `noUpClient-BD`/`-CD` — the `lpUpClient` position REFUTED on both legs.
--   §11 THE DISPATCH AND THE CLOSING THEOREM: `parked-at` splits all TEN
--       positions, `parked-of` is "stable ⟹ parked" at one leg, and
--       `stabR-final` is `stabR` at every reachable config from `LegJointB` +
--       `InFlightOpen` alone (no block, window or parked premise).
--
-- NOT delivered, and PRICED IN THE REPORT instead (`stableoffer-report.md`):
-- SIX of the eight in-flight positions (`InFlightOpen`, §11) — see §11's own
-- header for the two families and their different missing ingredients.  The
-- paragraph below is instalment 1's re-derivation of WHY, and it stands: the only
-- thing that has changed is that the gap is now a named, typed, six-field
-- interface with one of its siblings PROVED against it rather than prose.  The
-- reason is a
-- re-derivation finding, recorded here because it re-prices the campaign:
--
--   *** `LegInv` DOES NOT DETERMINE THE ENABLED MOVE. ***  The gate verdict's
--   §4 table has EIGHT components per row (producer phase, both BF servers,
--   both cells, both BF clients, relay phase) and it is the row that names the
--   enabled move.  `LegInv` (`LiveLegInv.AtPos`) carries ONE occupied slot plus
--   three COARSE driver facts (`ProdSent`/`RelayPre`-class/`InCp03`), and its
--   own header records the gap in as many words (§6 HONEST LIMITATION: "`AtPos
--   l lpUpCell` constrains the cell and the three drivers but says nothing
--   about `upClient`").  So at `lpUpCell` we cannot even show the TOKEN's own
--   next hop is enabled — the far-end BF client's position is unpinned — let
--   alone at `lpUpSrv` with a non-token payload in the cell (the H19 row).  The
--   progress half therefore needs a NEW co-position invariant (gate §7's clause
--   family 2, "every non-empty cell's payload is accepted by the peer at the
--   other end", plus the handshake-ladder co-positions the relay tail and the
--   whole down hop rest on).  That is a `LegInv`-level object with its own
--   preservation across every step class — NOT a `LiveStableOffer`-local cost,
--   and NOT dischargeable by editing anything from inside this module.
--
--   *** THE BLOCK IS NOT PINNED TO `blkA` BY `LegJoint`. ***  `LegInv l s =
--   Σ[ b ] Σ[ k ] AtPos l k b s` (existential `b`; only `lpPreSend` pins it),
--   `LegJoint l s = PipeInvS l s × LegInv l s × TokenExcl l s`, and `PipeInvS =
--   PipeInv⁺ × SrvCoupled` carries no value clause.  Two consequences: (a) the
--   parked offer at `lpDnClient` gives `dnClient l s ≡ bcBlk1 b`, which offers
--   `recvBFBlock · b` — NOT the `· blkA` the spec's `delivMenu` names; (b) the
--   `posProd` window cannot exclude `lpDone` without it (D past `cp3` having
--   stored some `b ≢ blkA` keeps `delivD` FALSE, so `specPos` still says
--   `posProd`).  Both are closed by ONE banked invariant, `PipeVal`
--   (`LTL/Value/PipeValInv.agda:163-171`): clause (7) `CliValOK (dnClient l s)`
--   for (a) and clause (8) `ConsDValOK (consOf l s)` for (b).  §2 therefore
--   takes `PipeVal l (toSys r)` as a hypothesis, and the FSim `Rel` must carry
--   it — a FIFTH gap beside the recorded G1-G4.  It is CHEAP: `PipeVal`'s own
--   per-step preserver is banked and UNCONDITIONAL
--   (`PipeValEvStep.stepEmitVᶠ : (l : TwoLegs) → StepEmitV l`, `:471-472`), and
--   it is already the driver of the banked `producedA` fold
--   (`PipeValWalk.agda:141`).
--   WHERE IT SHOWS UP in §5-§7: every premise below is `AtPos leg lpDnClient
--   blkA (toSys r)` — the parked position AT THE BLOCK THE SPEC NAMES, never at
--   an existential `b`.  That single hypothesis shape is what the widening owes
--   this module, and it is load-bearing in exactly one place: the kept receive
--   survives `∖ hidden blkA` because `keptB blkA (_ , apiBF l hi recvBFBlock)
--   blkA` computes to `⌊ blkA ≟ blkA ⌋` (`¬hidden-BD`/`¬hidden-CD`).  MEASURED
--   COROLLARY: the two links give DEFINITIONALLY EQUAL side conditions there
--   (both kept links satisfy `keptB`'s disjunct), so the block — not the link —
--   is the whole content of the hide condition.
--
-- ---------------------------------------------------------------------
-- §9 (package (2), DELIVERED): THE BLOCK PIN IS NO LONGER A PREMISE.  The
-- "FIFTH gap" above is closed: `LiveLegAssembly`'s §6b/§9 joins `PipeVal` to the
-- fold and carries BOTH legs (`LegJointB`), and §9 below turns the carried object
-- into §7's `blkA` premises — `parked-pin` does the pinning and
-- `stabOffer-from-joint` is the bridge.  CONSEQUENCE FOR PACKAGE (3): its
-- obligation is now BLOCK-FREE (`Parked l r = Σ[ b ] AtPos l lpDnClient b …`),
-- so the progress half never has to reason about payloads.
--
-- ---------------------------------------------------------------------
-- WHAT PACKAGE (3) MUST HIT.  The progress half's whole job is one implication,
-- and §9 has now weakened it to its block-FREE form.  *** IT IS WIRED AT EXACTLY
-- THIS TYPE *** — `stabOffer`/`stabOffer-parked`/`stabOffer-from-pin`/
-- `stabOffer-from-joint` all hand the `isStable` witness TO the premise
-- (instalment-3 fix; at `5ce4357` the documented interface carried the antecedent
-- while the wiring discarded it, so a correct R3′ lemma would not have composed):
--
--   isStable (radec r ∖ hidden blkA) → (q1 q2 q3 q4 : Bool)
--     → specPos r ≡ posProd q1 q2 q3 q4 → qᵢ ∧ qⱼ ≡ true → Parked leg r
--
-- (`Parked l r = Σ[ b ] AtPos l lpDnClient b (toSys r)`, §9 — block-FREE, so the
-- progress half never reasons about payloads).  The witness is INDISPENSABLE:
-- without stability the token may sit at any in-flight slot, and stability is
-- precisely what refutes the other slots by exhibiting an enabled hidden move.
--
-- i.e. "an obligated leg of a STABLE config is parked at D".  §2's `window⇒token`
-- already narrows the leg to the EIGHT in-flight slots and §1b already excludes
-- `lpDone`, so seven slots remain to be refuted by exhibiting an enabled hidden
-- move.  Two pieces of §5 are directly reusable there: `bundle-offer-recv` and
-- `consD-offer-recv` are generic in `(l, cl, sv)` and in the carried block, so
-- the `lpUpClient` arm (the same construction as the parked offer, with the RELAY
-- driver in place of D's) needs no new peer/bundle work.
--
-- ---------------------------------------------------------------------
-- ICE DISCIPLINE (the recorded hazard: a projection-like function applied to a
-- `with`-abstracted variable in a RESULT type).  `SpecOf r` IS `procOf (specPos
-- r)`, so a `with specPos r` under a goal mentioning `SpecOf r` is exactly the
-- forbidden shape.  Everything below therefore goes through the bridge pair
-- `OblOf` (a NAMED TOTAL predicate on `SpecPos`) + `stabOffer-at` (which
-- splits an EXPLICIT `k : SpecPos` argument, never a `with`-abstraction), and
-- the only `with specPos r` in the file sits at a goal whose type is
-- `OblOf (specPos r) …` — a named total function applied to the abstracted
-- term, which is the sanctioned form.
--
-- No postulates, holes, `--allow-unsolved-metas`, `NON_TERMINATING`, or
-- `mutual` blocks.  Every base module stays READ-ONLY.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer
  (blkA : Block₃) where

open import Level using ( 0ℓ; Lift; lift )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Bool using ( Bool; true; false; not; _∨_; _∧_; if_then_else_ )
open import Data.Maybe using ( just; nothing )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; trans; cong; subst )
open import Relation.Nullary using ( yes; no )
open import Class.DecEq using ( DecEq; _≟_ )

open import Process_Trees using ( PTree; ExtI; ptree; react; isStable )

------------------------------------------------------------------------
-- The shared alphabet and the CSP operator layer at it.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES; linkAB; linkAC; linkBD; linkCD; produce )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
import CSP.Examples.Cardano_network.BlockFetch p as BF

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( Stop; Skip; ∅v; ∅t; _∖_; _⦀_; _∥⇘_⇙_; Output-cont; viewV; EventSet )
open EventSet using ( mem )

------------------------------------------------------------------------
-- The LTS / stability / refusal vocabulary at that alphabet.
------------------------------------------------------------------------

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event√; evl; √; evLabel; ev; τ; _─[_]─►_; sRet; sVis; sTau; ev-inv )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step )
open import Semantics.Refusals {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Offers )
open import Semantics.Stability {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( mk-stable; stable-no-τ )

------------------------------------------------------------------------
-- The R2 decode carriers (state, reachable config, abstract decode) and the
-- per-leg invariant vocabulary.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( broken; decMed
        -- §11: the cell phase the two cell pins read
        ; CopyPhase; full )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
              ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              ; ConsDPh; consD; cph; cblk
              ; CScPos; CSsPos; BFcPos; BFsPos; InertPos
              ; bcBlk1; bcHead
              ; bsBlk1
        ; kac; kas; tsc; tss; lnc; lns; lfc; lfs
              ; decCons; decConsD
              -- §10: the relay driver's own decode and its two phase classes
              ; CPPh; consuming; producing; decCP )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD; phOf; InCp03 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; ProdSent; dnClient
        -- §10/§11: the relay slot the up-hop arm reads, and the two ⊥-lemmas
        -- that exclude `lpPreSend` / `lpDone` inside the obligated window
        ; relayOf; upClient; cellUp; cellDn
        ; prodSent-notSent-⊥; inCp03-recv-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( PipeVal; ConsValAt; ConsDValOK; consOf; pipeVal⇒client; relayBlk
        -- §11: the four value clauses the six open positions' pins read
        ; SrvValOK; CellValOK; RelayValOK )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
-- §11 (Task 4): the two per-leg link accessors the io fields' MANDATORY
-- unbrokenness antecedent is stated at (the same two links `Window` carries)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( LegInv; TokenSomewhere; legInv⇒token; AtPos; lpDnClient; ConsCp3
        -- §11: the WHOLE position datatype — the progress half dispatches on it
        ; LegPos; lpPreSend; lpUpSrv; lpUpCell; lpUpClient; lpRelayIn
        ; lpRelayOut; lpDnSrv; lpDnCell; lpDone; RelayCp3; RelayIn; RelayOut )
-- §9: the WIDENED joint invariant the future FSim `Rel` carries.  Imported for
-- ONE purpose — to type-check that the bridge below is fed by that very object.
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegAssembly blkA as LA

------------------------------------------------------------------------
-- The R2 STEP layer and the BANKED non-offer atoms the offer half consumes.
-- Every name below is READ, never edited: the `⦀`/`∥⇘`/`∖` intro lifts, the
-- abstract peer/bundle/node decodes, and the five non-offer families (protocol
-- mismatch `abs*-noBF`, direction `absBFs-dir-noBoth`, link `absBundleG-api-no`
-- and `drvD-{BD,CD}-no`, node fingerprint `absNode{A,B,C}-no-when-D`, medium
-- `medium-api-non-offer`).
------------------------------------------------------------------------

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( IoOffers; ⦀-noOffer; ⦀-ev-L; ⦀-ev-R; ∖-ev
                 ; lift-api-node-ev; lift-nodes-whole-ev
                 ; absBFc; absBundleG; absNodeA; absNodeB; absNodeC; absNodeD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( ApiHasLink; ahlBF; IsApiCSBF; aicBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  using ( aBFc; ceqBFc10 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( ≟-yes-refl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteKaTs blkA
  using ( absBFs-dir-noBoth )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( absKAc-noBF; absKAs-noBF; absCSc-noBF; absCSs-noBF
        ; absTSc-noBF; absTSs-noBF; absLNc-noBF; absLNs-noBF
        ; absLFc-noBF; absLFs-noBF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA
  using ( medium-api-non-offer; ApiIsCons; aicBFrecv
        ; absNodeA-no-when-D; absNodeB-no-when-D; absNodeC-no-when-D
        -- §10: the two RELAY-node rows of the same 12-way fingerprint family
        ; ApiIsProd
        ; absNodeA-no-when-B; absNodeC-no-when-B; absNodeD-no-when-B
        ; absNodeA-no-when-C; absNodeB-no-when-C; absNodeD-no-when-C )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( linkBD≢linkCD; linkAB≢linkBD; linkAC≢linkCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( absBundleG-api-no; drvD-BD-no; drvD-CD-no )
import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) as TLB
-- §10: the OUTER hide's τ-intro — a HIDDEN visible move of `radec r` is a τ of
-- `radec r ∖ hidden blkA`, which is what refutes stability
import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload}) as TLH

------------------------------------------------------------------------
-- The specification and the coupling.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( SpecProc; SpecMenu; Prod; LSpec; Done; delivMenu; _⊕v_; hidden )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveSpecCouple blkA
  using ( SpecPos; posIdle; posProd; posDone
        ; specPos; procOf; SpecOf
        ; mkPos; pastSend; pastRecv; prod1A; prod2A; g1F; g2F; delivD; recvOf
        ; fin8; ix0; blkA-refl )

------------------------------------------------------------------------
-- §0  Two Boolean micro-lemmas and one absurdity, used throughout.
------------------------------------------------------------------------

-- `true` is not `false` (the shape every payload-pin refutation ends in)
tf-⊥ : true ≡ false → ⊥
tf-⊥ ()

-- a `false` disjunction has both sides `false` (reads `delivD ≡ false` per leg)
∨-false : (x y : Bool) → (x ∨ y) ≡ false → (x ≡ false) × (y ≡ false)
∨-false false false _ = refl , refl
∨-false false true  ()
∨-false true  y     ()

-- a `true` negated disjunction has both sides `false` (reads `gᵢ ≡ true` as the
-- unbrokenness of that path's TWO links — this is the per-leg form of the gate
-- verdict's §2A "no break case space", and the per-leg form is all `stabR` gets:
-- `pᵢ ∧ gᵢ` says nothing about the OTHER leg's two links)
notOr-true : (x y : Bool) → not (x ∨ y) ≡ true → (x ≡ false) × (y ≡ false)
notOr-true false false _ = refl , refl
notOr-true false true  ()
notOr-true true  y     ()

------------------------------------------------------------------------
-- §1  The phase-threshold bridges between the COUPLING's Boolean flags
-- (`LiveSpecCouple.pastSend`/`pastRecv`) and the INVARIANT's `Set`-valued
-- classifiers (`PipeInv.ProdSent`, `WalkPr.InCp03`).
--
-- These are the two directions the campaign needs.  `pastSend⇒prodSent` is
-- what `stabR` consumes (the flag is given by `specPos`, the invariant premise
-- is wanted); `prodSent⇒pastSend` is the plan's Step-6 bridge, kept here
-- because it is the same ten-clause split and `LiveFSim`'s receive case needs
-- it to rule out the idle source position.
------------------------------------------------------------------------

-- flag `pᵢ` up ⇒ the producer has fired its `sendBFBlock` (`pp6 … pp9`)
pastSend⇒prodSent : (ph : ProdPh) → pastSend ph ≡ true → ProdSent ph
pastSend⇒prodSent pp0 ()
pastSend⇒prodSent pp1 ()
pastSend⇒prodSent pp2 ()
pastSend⇒prodSent pp3 ()
pastSend⇒prodSent pp4 ()
pastSend⇒prodSent pp5 ()
pastSend⇒prodSent pp6 _ = tt
pastSend⇒prodSent pp7 _ = tt
pastSend⇒prodSent pp8 _ = tt
pastSend⇒prodSent pp9 _ = tt

-- … and back: a producer past its send has the flag up (the Step-6 bridge)
prodSent⇒pastSend : (ph : ProdPh) → ProdSent ph → pastSend ph ≡ true
prodSent⇒pastSend pp0 ()
prodSent⇒pastSend pp1 ()
prodSent⇒pastSend pp2 ()
prodSent⇒pastSend pp3 ()
prodSent⇒pastSend pp4 ()
prodSent⇒pastSend pp5 ()
prodSent⇒pastSend pp6 _ = refl
prodSent⇒pastSend pp7 _ = refl
prodSent⇒pastSend pp8 _ = refl
prodSent⇒pastSend pp9 _ = refl

-- D's receive flag down ⇒ D is still pre-receive (`cp0 … cp3`)
pastRecv-false⇒inCp03 : (ph : ConsPh) → pastRecv ph ≡ false → InCp03 ph
pastRecv-false⇒inCp03 cp0 _ = tt
pastRecv-false⇒inCp03 cp1 _ = tt
pastRecv-false⇒inCp03 cp2 _ = tt
pastRecv-false⇒inCp03 cp3 _ = tt
pastRecv-false⇒inCp03 cp4 ()
pastRecv-false⇒inCp03 cp5 ()
pastRecv-false⇒inCp03 cp6 ()

------------------------------------------------------------------------
-- §1b  THE `lpDone` EXCLUSION, and why it needs `PipeVal`.
--
-- `recvOf (consD b ph) = if pastRecv ph then ⌊ b ≟ blkA ⌋ else false`
-- (`LiveSpecCouple.agda:181-182`), so `recvOf ≡ false` does NOT by itself give
-- `pastRecv ph ≡ false`: a D driver PAST `cp3` holding some `b ≢ blkA` also
-- reads `false`, and at such a state `specPos` still says `posProd` while the
-- leg is discharged and offers nothing.  `PipeVal`'s clause (8)
-- (`ConsDValOK (consOf l s)` = `ConsValAt (cblk …) (cph …)`, which IS `b ≡ blkA`
-- from `cp4` on) removes exactly that state.
------------------------------------------------------------------------

-- read `PipeVal`'s eighth clause off the tuple (the accessor `PipeValInv` uses
-- inline in `pipeVal⇒recorded`, named here so no consumer repeats seven `proj₂`s)
pipeVal-cons : (l : TwoLegs) (s : SysState) → PipeVal l s → ConsDValOK (consOf l s)
pipeVal-cons l s (_ , _ , _ , _ , _ , _ , _ , h8) = h8

-- a value-correct D driver whose receive flag is down really is pre-receive
recvOf-false⇒inCp03 : (x : ConsDPh) → ConsDValOK x → recvOf x ≡ false → InCp03 (cph x)
recvOf-false⇒inCp03 (consD b cp0) _    _ = tt
recvOf-false⇒inCp03 (consD b cp1) _    _ = tt
recvOf-false⇒inCp03 (consD b cp2) _    _ = tt
recvOf-false⇒inCp03 (consD b cp3) _    _ = tt
recvOf-false⇒inCp03 (consD b cp4) refl e = ⊥-elim (tf-⊥ (trans (sym blkA-refl) e))
recvOf-false⇒inCp03 (consD b cp5) refl e = ⊥-elim (tf-⊥ (trans (sym blkA-refl) e))
recvOf-false⇒inCp03 (consD b cp6) refl e = ⊥-elim (tf-⊥ (trans (sym blkA-refl) e))

------------------------------------------------------------------------
-- §2  THE OBLIGATED-WINDOW READER.
--
-- `specPos r ≡ posProd q1 q2 q3 q4` is the ONLY thing `stabR` is handed about
-- the spec side, and `delivMenu` gates the BD receive on `q1 ∧ q2` and the CD
-- receive on `q3 ∧ q4`.  So the window reader's job is: from that equation plus
-- the two flags of ONE leg, produce that leg's component facts.  Three
-- inversions of `mkPos` do the work; each is a four-clause split following
-- `mkPos`'s own clause order (`LiveSpecCouple.agda:193-197`).
------------------------------------------------------------------------

-- `posProd` is not `mkPos`'s delivered clause, so nothing has been delivered
mkPos-prod-dl : (dl p1 g1 p2 g2 : Bool) {q1 q2 q3 q4 : Bool}
              → mkPos dl p1 g1 p2 g2 ≡ posProd q1 q2 q3 q4 → dl ≡ false
mkPos-prod-dl true  p1    g1 p2    g2 ()
mkPos-prod-dl false true  g1 p2    g2 _ = refl
mkPos-prod-dl false false g1 true  g2 _ = refl
mkPos-prod-dl false false g1 false g2 ()

-- the reported `q1` IS the `p1` flag `mkPos` was given
mkPos-prod-p1 : (dl p1 g1 p2 g2 : Bool) {q1 q2 q3 q4 : Bool}
              → mkPos dl p1 g1 p2 g2 ≡ posProd q1 q2 q3 q4 → q1 ≡ p1
mkPos-prod-p1 true  p1    g1 p2    g2 ()
mkPos-prod-p1 false true  g1 p2    g2 refl = refl
mkPos-prod-p1 false false g1 true  g2 refl = refl
mkPos-prod-p1 false false g1 false g2 ()

-- the reported `q2` IS the `g1` flag (both surviving clauses pass it through)
mkPos-prod-g1 : (dl p1 g1 p2 g2 : Bool) {q1 q2 q3 q4 : Bool}
              → mkPos dl p1 g1 p2 g2 ≡ posProd q1 q2 q3 q4 → q2 ≡ g1
mkPos-prod-g1 true  p1    g1 p2    g2 ()
mkPos-prod-g1 false true  g1 p2    g2 refl = refl
mkPos-prod-g1 false false g1 true  g2 refl = refl
mkPos-prod-g1 false false g1 false g2 ()

-- the reported `q3` IS the `p2` flag
mkPos-prod-p2 : (dl p1 g1 p2 g2 : Bool) {q1 q2 q3 q4 : Bool}
              → mkPos dl p1 g1 p2 g2 ≡ posProd q1 q2 q3 q4 → q3 ≡ p2
mkPos-prod-p2 true  p1    g1 p2    g2 ()
mkPos-prod-p2 false true  g1 p2    g2 refl = refl
mkPos-prod-p2 false false g1 true  g2 refl = refl
mkPos-prod-p2 false false g1 false g2 ()

-- the reported `q4` IS the `g2` flag
mkPos-prod-g2 : (dl p1 g1 p2 g2 : Bool) {q1 q2 q3 q4 : Bool}
              → mkPos dl p1 g1 p2 g2 ≡ posProd q1 q2 q3 q4 → q4 ≡ g2
mkPos-prod-g2 true  p1    g1 p2    g2 ()
mkPos-prod-g2 false true  g1 p2    g2 refl = refl
mkPos-prod-g2 false false g1 true  g2 refl = refl
mkPos-prod-g2 false false g1 false g2 ()

-- THE WINDOW, as one record: what a leg's own `pᵢ ∧ gᵢ` buys.  `wSent`/`wPend`
-- are exactly `legInv⇒token`'s two premises; `wLink1`/`wLink2` are the leg's
-- two links unbroken (needed by every io-class enabled move, since a broken
-- link's medium is `Skip` and offers nothing at all).
record Window (l : TwoLegs) (s : SysState) (k1 k2 : Link) : Set where
  constructor mkWindow
  field
    wSent  : ProdSent (prodOf l s)
    wPend  : InCp03 (phOf l s)
    wLink1 : broken (med s) k1 ≡ false
    wLink2 : broken (med s) k2 ≡ false
open Window public

-- LEG BD: the spec position plus `q1 ∧ q2` (as two equations, which is how the
-- `delivMenu` gate will hand them over) plus `PipeVal` give leg BD's window.
window-BD : (r : RState) {q1 q2 q3 q4 : Bool}
          → specPos r ≡ posProd q1 q2 q3 q4
          → q1 ≡ true → q2 ≡ true
          → PipeVal legBD (toSys r)
          → Window legBD (toSys r) linkAB linkBD
window-BD r {q1} {q2} eq h1 h2 pv =
  mkWindow
    (pastSend⇒prodSent (prodOf legBD (toSys r))
       (trans (sym (mkPos-prod-p1 (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                      (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                      (g2F (broken (med (toSys r)))) eq)) h1))
    (recvOf-false⇒inCp03 (consOf legBD (toSys r))
       (pipeVal-cons legBD (toSys r) pv)
       (proj₁ (∨-false (recvOf (consOf legBD (toSys r)))
                       (recvOf (consOf legCD (toSys r)))
                       (mkPos-prod-dl (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                          (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                          (g2F (broken (med (toSys r)))) eq))))
    (proj₁ (notOr-true (broken (med (toSys r)) linkAB) (broken (med (toSys r)) linkBD)
              (trans (sym (mkPos-prod-g1 (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                             (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                             (g2F (broken (med (toSys r)))) eq)) h2)))
    (proj₂ (notOr-true (broken (med (toSys r)) linkAB) (broken (med (toSys r)) linkBD)
              (trans (sym (mkPos-prod-g1 (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                             (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                             (g2F (broken (med (toSys r)))) eq)) h2)))

-- LEG CD: the mirror, off `q3 ∧ q4` and the AC/CD links
window-CD : (r : RState) {q1 q2 q3 q4 : Bool}
          → specPos r ≡ posProd q1 q2 q3 q4
          → q3 ≡ true → q4 ≡ true
          → PipeVal legCD (toSys r)
          → Window legCD (toSys r) linkAC linkCD
window-CD r {q3 = q3} {q4} eq h3 h4 pv =
  mkWindow
    (pastSend⇒prodSent (prodOf legCD (toSys r))
       (trans (sym (mkPos-prod-p2 (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                      (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                      (g2F (broken (med (toSys r)))) eq)) h3))
    (recvOf-false⇒inCp03 (consOf legCD (toSys r))
       (pipeVal-cons legCD (toSys r) pv)
       (proj₂ (∨-false (recvOf (consOf legBD (toSys r)))
                       (recvOf (consOf legCD (toSys r)))
                       (mkPos-prod-dl (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                          (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                          (g2F (broken (med (toSys r)))) eq))))
    (proj₁ (notOr-true (broken (med (toSys r)) linkAC) (broken (med (toSys r)) linkCD)
              (trans (sym (mkPos-prod-g2 (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                             (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                             (g2F (broken (med (toSys r)))) eq)) h4)))
    (proj₂ (notOr-true (broken (med (toSys r)) linkAC) (broken (med (toSys r)) linkCD)
              (trans (sym (mkPos-prod-g2 (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                             (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                             (g2F (broken (med (toSys r)))) eq)) h4)))

-- THE POSITIVE TOKEN LOCATION at an obligated leg: the window's two component
-- facts are exactly `legInv⇒token`'s premises, so the token is in one of the
-- EIGHT in-flight slots.  This is the composition the progress half dispatches
-- over — and the point at which the finding recorded in the header bites: the
-- eight arms are BARE OCCUPANCY facts, so they locate the token without
-- determining which move is enabled.
window⇒token : (l : TwoLegs) (s : SysState) {k1 k2 : Link}
             → LegInv l s → Window l s k1 k2 → TokenSomewhere l s
window⇒token l s li w = legInv⇒token l s li (wSent w) (wPend w)

------------------------------------------------------------------------
-- §3  THE SPEC SIDE — the τ*-settled branch, its stability, its offers.
--
-- Every spec state is a pure internal choice `react ∅v τmap` over eight
-- branches whose successors are all `react … ∅t`, i.e. STABLE.  So the settled
-- state is one τ away and the choice of BRANCH is the whole content:
--
--   `posIdle` — `idleτ … (lift ix0) = just Stop` (`Spec.lagda.md:317`)
--   `posDone` — `Done`'s branch 0 is `just Stop` (`:164-170`)
--   `posProd` — `prodτ … (lift ix0) = just (ptree (react (delivMenu …) ∅t))`
--               (`:269-270`)
--
-- Branch 0 is also the MINIMAL choice at `posProd` (branches 1-6 are
-- `delivMenu ⊕v {one break / one produce}` and branch 7 is
-- `delivMenu blkA true true true true`, all supersets), but minimality is an
-- ECONOMY choice, not a soundness requirement — see the falsification note at
-- the foot of this module.
------------------------------------------------------------------------

-- the `stabR` payload at one (spec, impl) pair: a τ*-settled stable spec state
-- whose offers the implementation covers
Settle : SpecProc → NetProc → Set₁
Settle q p = Σ[ q′ ∈ SpecProc ]
               ( (q ─[τ*]─► q′)
               × isStable q′
               × (∀ (e : Event√ (⊤ {0ℓ})) → Offers q′ e → Offers p e) )

-- the refusing spec state, at the spec's own process type
StopS : SpecProc
StopS = Stop

-- `Stop` is stable: `force Stop = react ∅v ∅t` and `∅t` is everywhere `nothing`
stopS-stable : isStable StopS
stopS-stable = mk-stable {t = StopS} refl (λ i a → refl)

-- `Stop` offers nothing at all: its visible map is `∅v`, and it cannot `√`
-- (its force is a `react`, not a `ret`)
stopS-no-offer : (e : Event√ (⊤ {0ℓ})) → Offers StopS e → ⊥
stopS-no-offer (evl (evLabel X ee a)) (t′ , st) with ev-inv st
... | _ , _ , refl , ()
stopS-no-offer (√ x) (t′ , sRet ())

-- ARM 1 (`posIdle`): the idle spec settles on `Stop`, so the containment is
-- VACUOUS — `stabR` at an idle position asks nothing of the implementation.
-- This is `LSpec`'s "no obligation" in machine-checked form.
settle-idle : (g1 g2 : Bool) (P : NetProc) → Settle (LSpec blkA g1 g2) P
settle-idle g1 g2 P =
    StopS
  , τ*-step (sTau {i = fin8} {a = lift ix0} refl refl) τ*-refl
  , stopS-stable
  , λ e o → ⊥-elim (stopS-no-offer e o)

-- ARM 2 (`posDone`): `Done` is the `⊑FD`-top — its branch 0 is `Stop` too, so
-- the discharged position is likewise free
settle-done : (P : NetProc) → Settle (Done blkA) P
settle-done P =
    StopS
  , τ*-step (sTau {i = fin8} {a = lift ix0} refl refl) τ*-refl
  , stopS-stable
  , λ e o → ⊥-elim (stopS-no-offer e o)

-- the settled state of a PRODUCED position: `prodτ`'s branch 0, whose visible
-- map IS `delivMenu` and whose τ-map is `∅t`
prodBr0 : (p1 g1 p2 g2 : Bool) → SpecProc
prodBr0 p1 g1 p2 g2 = ptree (react (delivMenu blkA p1 g1 p2 g2) ∅t)

-- branch 0 is stable (`∅t` everywhere `nothing`) — this is why ONE τ suffices
prodBr0-stable : (p1 g1 p2 g2 : Bool) → isStable (prodBr0 p1 g1 p2 g2)
prodBr0-stable p1 g1 p2 g2 = mk-stable {t = prodBr0 p1 g1 p2 g2} refl (λ i a → refl)

-- THE RESIDUAL OBLIGATION, and the whole remaining content of `stabR`: every
-- offer of branch 0's menu is an offer of the implementation.  Stated over the
-- MENU rather than over two hand-written events, so that the flag gating and
-- the payload gating stay where the spec put them (`delivMenu`) and no event
-- bookkeeping is duplicated here.
DelivObl : Bool → Bool → Bool → Bool → NetProc → Set₁
DelivObl p1 g1 p2 g2 P =
  ∀ {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {t′ : SpecProc}
  → delivMenu blkA p1 g1 p2 g2 (X , ee) a ≡ just t′
  → Offers P (evl (evLabel X ee a))

-- branch 0's containment, from the residual obligation: an offer of a `react`
-- node is a `just` in its visible map (`ev-inv`), and `√` is refuted by the
-- same `react` force
settle-prod-cont : (p1 g1 p2 g2 : Bool) (P : NetProc)
                 → DelivObl p1 g1 p2 g2 P
                 → (e : Event√ (⊤ {0ℓ})) → Offers (prodBr0 p1 g1 p2 g2) e → Offers P e
settle-prod-cont p1 g1 p2 g2 P obl (evl (evLabel X ee a)) (t′ , st) with ev-inv st
... | _ , _ , refl , br = obl br
settle-prod-cont p1 g1 p2 g2 P obl (√ x) (t′ , sRet ())

-- ARM 3 (`posProd`): the produced spec settles on branch 0, and `stabR` reduces
-- EXACTLY to `DelivObl`
settle-prod : (p1 g1 p2 g2 : Bool) (P : NetProc)
            → DelivObl p1 g1 p2 g2 P → Settle (Prod blkA p1 g1 p2 g2) P
settle-prod p1 g1 p2 g2 P obl =
    prodBr0 p1 g1 p2 g2
  , τ*-step (sTau {i = fin8} {a = lift ix0} refl refl) τ*-refl
  , prodBr0-stable p1 g1 p2 g2
  , settle-prod-cont p1 g1 p2 g2 P obl

------------------------------------------------------------------------
-- §4  THE DISPATCH — `stabR` at a reachable config, reduced to `DelivObl`.
------------------------------------------------------------------------

-- the `stabR` obligation at one reachable config, in the FSim's own coordinates
StabOffer : RState → Set₁
StabOffer r = isStable (radec r ∖ hidden blkA)
            → Settle (SpecOf r) (radec r ∖ hidden blkA)

-- what each spec position demands of the implementation: nothing at all off
-- `posProd` (both other branches settle on `Stop`).  A NAMED TOTAL predicate —
-- this is the ICE-safe carrier the `with specPos r` below abstracts over.
OblOf : SpecPos → NetProc → Set₁
OblOf (posIdle g1 g2)       P = ⊤
OblOf (posProd p1 g1 p2 g2) P = DelivObl p1 g1 p2 g2 P
OblOf posDone               P = ⊤

-- the dispatch on an EXPLICIT position argument (never a `with`-abstraction, so
-- the goal's `SpecOf r` is transported by an ordinary `subst` on `procOf`)
stabOffer-at : (r : RState) (k : SpecPos) → specPos r ≡ k
             → OblOf k (radec r ∖ hidden blkA) → StabOffer r
stabOffer-at r (posIdle g1 g2) eq _ _ =
  subst (λ q → Settle q (radec r ∖ hidden blkA)) (sym (cong procOf eq))
        (settle-idle g1 g2 (radec r ∖ hidden blkA))
stabOffer-at r (posProd p1 g1 p2 g2) eq obl _ =
  subst (λ q → Settle q (radec r ∖ hidden blkA)) (sym (cong procOf eq))
        (settle-prod p1 g1 p2 g2 (radec r ∖ hidden blkA) obl)
stabOffer-at r posDone eq _ _ =
  subst (λ q → Settle q (radec r ∖ hidden blkA)) (sym (cong procOf eq))
        (settle-done (radec r ∖ hidden blkA))

-- collect the per-position demand: only `posProd` asks anything, and it asks
-- with its own four flags.  The one `with specPos r` in the module, at a goal
-- whose type is `OblOf` (a named total function) applied to the abstracted term.
oblOf-of : (r : RState)
         → ((q1 q2 q3 q4 : Bool) → specPos r ≡ posProd q1 q2 q3 q4
              → DelivObl q1 q2 q3 q4 (radec r ∖ hidden blkA))
         → OblOf (specPos r) (radec r ∖ hidden blkA)
-- NOTE the `refl`: the `with`-abstraction of `specPos r` rewrites the goal AND
-- the hypothesis `h` (whose type mentions `specPos r`), so in the `posProd` arm
-- `h` already expects `posProd p1 g1 p2 g2 ≡ posProd p1 g1 p2 g2`.  Passing a
-- `… in eq` witness there is a type error — the abstraction has already done
-- the rewriting that `eq` was meant to perform.
oblOf-of r h with specPos r
... | posIdle g1 g2       = tt
... | posProd p1 g1 p2 g2 = h p1 g1 p2 g2 refl
... | posDone             = tt

-- *** THE HEADLINE OF THIS INSTALMENT ***  `stabR` at every reachable config,
-- modulo ONE residual premise demanded only at produced positions.  The idle
-- and discharged positions are DISCHARGED HERE, unconditionally.
--
-- *** THE `isStable` WITNESS IS THREADED INTO THE PREMISE *** (instalment-3 fix,
-- from the review).  `StabOffer r` IS `isStable P → Settle …`, and `stabOffer-at`
-- discards that witness in all three clauses — so if the residual premise were
-- stated WITHOUT the antecedent, the progress half would owe a witness-free
-- `Parked`, which is UNPROVABLE (without stability the token may sit at any
-- in-flight slot; stability is exactly what refutes the other slots by exhibiting
-- an enabled hidden move).  Threading it here is what makes the documented
-- interface and the wiring the SAME type.  A caller who does not need the witness
-- instantiates with `λ _ → h`, so nothing is lost.
stabOffer : (r : RState)
          → (isStable (radec r ∖ hidden blkA)
               → (q1 q2 q3 q4 : Bool) → specPos r ≡ posProd q1 q2 q3 q4
               → DelivObl q1 q2 q3 q4 (radec r ∖ hidden blkA))
          → StabOffer r
stabOffer r h st = stabOffer-at r (specPos r) refl (oblOf-of r (h st)) st

------------------------------------------------------------------------
-- §5  THE PARKED OFFER — the implementation side at `lpDnClient` (O1-O6).
--
-- At the parked position the token sits in D's BF client (`bcBlk1 b`) AND D's
-- own consume driver is at `cp3`, so BOTH operands of node D's api sync offer
-- the kept receive: the client because `bcAblk b`'s only api edge IS
-- `recvBFBlock` at `b` (`ceqBFc10`), the driver because `decCons … cp3` is a
-- bare `Prefix` on `recvBFBlock` (no value gate at all).  Everything else is
-- the SYNC/SOLO ladder up the `⦀` / `∥⇘apiES⇙` / `∥⇘ioES⇙` / `∖` stack, which
-- needs a NON-OFFER for every idle sibling: eleven inside the 12-peer bundle,
-- the other bundle and the other consume driver inside node D, the three
-- sibling NODES, and the medium.  Every one of those is BANKED and merely
-- applied here — protocol mismatch (`abs*-noBF`), direction
-- (`absBFs-dir-noBoth`, `cl ≢ sv`), link (`absBundleG-api-no`,
-- `drvD-{BD,CD}-no`), node role/link fingerprint (`absNode{A,B,C}-no-when-D`)
-- and "the medium fires no api at all" (`medium-api-non-offer`).
--
-- NOTE ON TYPES: `IoOffers P e a` (`SysStep.agda:386-387`) and
-- `Offers P (evl (evLabel _ e a))` (`Semantics/Refusals.agda:19-20`) are the
-- SAME Σ-type, so the pieces below are stated in the `IoOffers` vocabulary the
-- banked atoms use and consumed where `DelivObl` asks for `Offers`.
------------------------------------------------------------------------

-- O1  the BF CLIENT's own offer: a client holding `b` (`bcBlk1 b`, coarsening to
-- `bcAblk b`) offers the api receive OF THAT BLOCK and lands on its streaming
-- head (`bfCfin (bcAblk b) ≡ false` is `refl`; the edge is `ceqBFc10`)
bfc-offer-recv : (l : Link) (d : Dir) (b : Block₃)
               → IoOffers (absBFc l d (bcBlk1 b)) (apiBF l d recvBFBlock) b
bfc-offer-recv l d b =
    absBFc l d (bcHead BF.stStreaming)
  , aBFc l d (bcBlk1 b) (bcHead BF.stStreaming) refl (ceqBFc10 l d)

-- O2  the 12-peer BUNDLE's offer: lift O1 past the four peers listed before the
-- BF client (KA×2, CS×2, each by `⦀-ev-R`) and the seven listed after it (one
-- composed `⦀-noOffer` chain — the BF SERVER by its direction, the other ten by
-- protocol mismatch)
bundle-offer-recv : (l : Link) (cl sv : Dir) (cl≢sv : cl ≢ sv)
     (csc : CScPos) (css : CSsPos) (b : Block₃) (bfs : BFsPos) (ip : InertPos)
   → IoOffers (absBundleG l cl sv csc css (bcBlk1 b) bfs ip)
              (apiBF l cl recvBFBlock) b
bundle-offer-recv l cl sv cl≢sv csc css b bfs ip =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _
          (⦀-ev-R _ _
            (⦀-ev-L _ _ (proj₂ (bfc-offer-recv l cl b))
              (noOffer→viewV _
                (⦀-noOffer _ _ (absBFs-dir-noBoth l sv bfs (BF.apiBFev l cl recvBFBlock) cl≢sv)
                 (⦀-noOffer _ _ (absTSc-noBF l cl (tsc ip) (BF.apiBFev l cl recvBFBlock))
                  (⦀-noOffer _ _ (absTSs-noBF l sv (tss ip) (BF.apiBFev l cl recvBFBlock))
                   (⦀-noOffer _ _ (absLNc-noBF l cl (lnc ip) (BF.apiBFev l cl recvBFBlock))
                    (⦀-noOffer _ _ (absLNs-noBF l sv (lns ip) (BF.apiBFev l cl recvBFBlock))
                     (⦀-noOffer _ _ (absLFc-noBF l cl (lfc ip) (BF.apiBFev l cl recvBFBlock))
                                    (absLFs-noBF l sv (lfs ip) (BF.apiBFev l cl recvBFBlock))))))))))
            (noOffer→viewV _ (absCSs-noBF l sv css (BF.apiBFev l cl recvBFBlock))))
          (noOffer→viewV _ (absCSc-noBF l cl csc (BF.apiBFev l cl recvBFBlock))))
        (noOffer→viewV _ (absKAs-noBF l sv (kas ip) (BF.apiBFev l cl recvBFBlock))))
      (noOffer→viewV _ (absKAc-noBF l cl (kac ip) (BF.apiBFev l cl recvBFBlock)))

-- the `cp3` consume decode's visible map AT the kept receive, for ANY carried
-- block: `decCons l hi b₀ cp3` is a bare `Prefix`, so the continuation is the
-- `cp4` decode STORING the received value.  Link-GENERIC — the concrete-link
-- instance is `refl` (`LiveSpecCouple.consOffer-cp3`), the generic one needs
-- `≟-yes-refl` to unstick `l ≟ l` inside `Net_Api-≟`
consVis-cp3 : (l : Link) (b₀ x : Block₃)
  → viewV (PTree.force (decCons l hi b₀ cp3)) (Block₃ , apiBF l hi recvBFBlock) x
    ≡ just (decCons l hi x cp4)
consVis-cp3 l b₀ x rewrite ≟-yes-refl l = refl

-- O3  node D's consume DRIVER at `cp3` offers the api receive of ANY block: the
-- inner `decCons` step propagates through the `>> Skip` bind (`bind-ev`)
consD-offer-recv : (l : Link) (b₀ x : Block₃)
                 → IoOffers (decConsD l (consD b₀ cp3)) (apiBF l hi recvBFBlock) x
consD-offer-recv l b₀ x =
    _
  , TLB.bind-ev (λ _ → Skip) (decCons l hi b₀ cp3) (sVis refl (consVis-cp3 l b₀ x))

-- the node-D api FINGERPRINT of the kept receive, built WITHOUT a firing step:
-- `recvBFBlock` is a client-role tag and the link is the leg's own.  This is
-- exactly the hypothesis the three sibling-node non-offers demand.
fpD-BD : ApiIsCons (apiBF linkBD hi recvBFBlock)
       × (ApiHasLink linkBD (apiBF linkBD hi recvBFBlock)
          ⊎ ApiHasLink linkCD (apiBF linkBD hi recvBFBlock))
fpD-BD = aicBFrecv , inj₁ ahlBF

-- … and the CD-leg mirror
fpD-CD : ApiIsCons (apiBF linkCD hi recvBFBlock)
       × (ApiHasLink linkBD (apiBF linkCD hi recvBFBlock)
          ⊎ ApiHasLink linkCD (apiBF linkCD hi recvBFBlock))
fpD-CD = aicBFrecv , inj₂ ahlBF

-- a `cp3` driver IS the `cp3` driver at its own stored block (the η the field
-- equation needs before `subst` can retarget `decConsD`)
consCp3⇒form : (x : ConsDPh) → ConsCp3 (cph x) → x ≡ consD (cblk x) cp3
consCp3⇒form (consD b cp0) ()
consCp3⇒form (consD b cp1) ()
consCp3⇒form (consD b cp2) ()
consCp3⇒form (consD b cp3) _ = refl
consCp3⇒form (consD b cp4) ()
consCp3⇒form (consD b cp5) ()
consCp3⇒form (consD b cp6) ()

-- the kept receive is NOT hidden: `keptB blkA (_ , apiBF linkBD hi recvBFBlock)
-- blkA` computes to `⌊ blkA ≟ blkA ⌋` (both link tests and the dir test are
-- concrete), which `blkA-refl` says is `true`.  THE BLOCK PIN IS WHAT BUYS THIS.
¬hidden-BD : mem (hidden blkA) (Block₃ , apiBF linkBD hi recvBFBlock) blkA → ⊥
¬hidden-BD e = tf-⊥ (trans (sym blkA-refl) e)

-- … and the CD-leg mirror (the second disjunct of `keptB`'s link test)
¬hidden-CD : mem (hidden blkA) (Block₃ , apiBF linkCD hi recvBFBlock) blkA → ⊥
¬hidden-CD e = tf-⊥ (trans (sym blkA-refl) e)

------------------------------------------------------------------------
-- §6  THE LADDER — node D, the four-node interleave, the io gate, both hides.
--
-- The node-level lemmas take the node state ABSTRACT plus the two FIELD
-- equations the invariant supplies, and retarget the two generic offers of §5
-- by `subst` on a one-field motive.  Writing them this way (rather than over a
-- literal `mkNodeD`) is what keeps the call site free of any `with` on a
-- projection of `toSys r` — the recorded ICE shape.
------------------------------------------------------------------------

-- NODE D, leg BD: the driver↔peer api SYNC (`lift-api-node-ev`, `apiES`
-- membership is literally `tt`), past node D's OTHER bundle and OTHER consume
-- driver — both pinned to `linkCD`, so both are refuted by the link mismatch
nodeD-offer-BD : (nd : SN.NodeStateD) (b b₀ : Block₃)
  → SN.NodeStateD.bfC-BD nd ≡ bcBlk1 b
  → SN.NodeStateD.cons-BD nd ≡ consD b₀ cp3
  → IoOffers (absNodeD nd) (apiBF linkBD hi recvBFBlock) b
nodeD-offer-BD nd b b₀ hcli hcons =
    _
  , lift-api-node-ev _ _ tt
      (⦀-ev-L _ _ (proj₂ bOff)
        (noOffer→viewV _
          (absBundleG-api-no linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd)
             (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd)
             ahlBF linkBD≢linkCD tt)))
      (⦀-ev-L _ _ (proj₂ dOff) (noOffer→viewV _ (drvD-CD-no nd ahlBF)))
  where
  -- the leg's own bundle offers the receive, at the client position the
  -- invariant names
  bOff : IoOffers (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
                     (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
                  (apiBF linkBD hi recvBFBlock) b
  bOff = subst (λ q → IoOffers (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd)
                                  (SN.NodeStateD.csS-BD nd) q (SN.NodeStateD.bfS-BD nd)
                                  (SN.NodeStateD.inert-BD nd))
                               (apiBF linkBD hi recvBFBlock) b)
               (sym hcli)
               (bundle-offer-recv linkBD hi lo (λ ()) (SN.NodeStateD.csC-BD nd)
                  (SN.NodeStateD.csS-BD nd) b (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd))
  -- … and so does the leg's own consume driver, at `cp3`
  dOff : IoOffers (decConsD linkBD (SN.NodeStateD.cons-BD nd)) (apiBF linkBD hi recvBFBlock) b
  dOff = subst (λ q → IoOffers (decConsD linkBD q) (apiBF linkBD hi recvBFBlock) b)
               (sym hcons) (consD-offer-recv linkBD b₀ b)

-- NODE D, leg CD: the mirror (both node-D operands are `⦀-ev-R` here, and the
-- sibling pins are the `linkBD` ones)
nodeD-offer-CD : (nd : SN.NodeStateD) (b b₀ : Block₃)
  → SN.NodeStateD.bfC-CD nd ≡ bcBlk1 b
  → SN.NodeStateD.cons-CD nd ≡ consD b₀ cp3
  → IoOffers (absNodeD nd) (apiBF linkCD hi recvBFBlock) b
nodeD-offer-CD nd b b₀ hcli hcons =
    _
  , lift-api-node-ev _ _ tt
      (⦀-ev-R _ _ (proj₂ bOff)
        (noOffer→viewV _
          (absBundleG-api-no linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
             (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)
             ahlBF (λ q → linkBD≢linkCD (sym q)) tt)))
      (⦀-ev-R _ _ (proj₂ dOff) (noOffer→viewV _ (drvD-BD-no nd ahlBF)))
  where
  -- the CD bundle's offer at the invariant's client position
  bOff : IoOffers (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd)
                     (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
                  (apiBF linkCD hi recvBFBlock) b
  bOff = subst (λ q → IoOffers (absBundleG linkCD hi lo (SN.NodeStateD.csC-CD nd)
                                  (SN.NodeStateD.csS-CD nd) q (SN.NodeStateD.bfS-CD nd)
                                  (SN.NodeStateD.inert-CD nd))
                               (apiBF linkCD hi recvBFBlock) b)
               (sym hcli)
               (bundle-offer-recv linkCD hi lo (λ ()) (SN.NodeStateD.csC-CD nd)
                  (SN.NodeStateD.csS-CD nd) b (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
  -- … and the CD consume driver's
  dOff : IoOffers (decConsD linkCD (SN.NodeStateD.cons-CD nd)) (apiBF linkCD hi recvBFBlock) b
  dOff = subst (λ q → IoOffers (decConsD linkCD q) (apiBF linkCD hi recvBFBlock) b)
               (sym hcons) (consD-offer-recv linkCD b₀ b)

-- THE FOUR-NODE INTERLEAVE: node D is the LAST operand, so the lift is three
-- `⦀-ev-R`s, each discharged by that sibling's api fingerprint clash with D's
-- (`recvBFBlock` is a CONSUMER tag on a D link — A is a pure producer, B and C
-- are producers on their down link and consumers on their up link)
nodes-offer-BD : (s : SysState) (b : Block₃)
  → IoOffers (absNodeD (nD s)) (apiBF linkBD hi recvBFBlock) b
  → IoOffers (absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))))
             (apiBF linkBD hi recvBFBlock) b
nodes-offer-BD s b (M , st) =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ st (noOffer→viewV _ (absNodeC-no-when-D (nC s) tt fpD-BD)))
        (noOffer→viewV _ (absNodeB-no-when-D (nB s) tt fpD-BD)))
      (noOffer→viewV _ (absNodeA-no-when-D (nA s) tt fpD-BD))

-- … the CD-leg mirror (same ladder, the CD fingerprint)
nodes-offer-CD : (s : SysState) (b : Block₃)
  → IoOffers (absNodeD (nD s)) (apiBF linkCD hi recvBFBlock) b
  → IoOffers (absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s))))
             (apiBF linkCD hi recvBFBlock) b
nodes-offer-CD s b (M , st) =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-R _ _ st (noOffer→viewV _ (absNodeC-no-when-D (nC s) tt fpD-CD)))
        (noOffer→viewV _ (absNodeB-no-when-D (nB s) tt fpD-CD)))
      (noOffer→viewV _ (absNodeA-no-when-D (nA s) tt fpD-CD))

-- THE WHOLE HIDDEN ABSTRACTION, leg BD: solo through the io gate (the medium
-- fires NO api event at all — `medium-api-non-offer`), keep across `∖ ioES`
-- (an api event is not in `ioES`, `λ ()`), keep across `∖ hidden blkA` (the BD
-- receive OF `blkA` is KEPT — this is the step the block pin pays for)
whole-offer-BD : (r : RState)
  → IoOffers (absNodeD (nD (toSys r))) (apiBF linkBD hi recvBFBlock) blkA
  → IoOffers (radec r ∖ hidden blkA) (apiBF linkBD hi recvBFBlock) blkA
whole-offer-BD r off =
    _
  , ∖-ev (hidden blkA) (radec r) ¬hidden-BD
      (lift-nodes-whole-ev (decMed (med (toSys r))) _ (λ ())
        (proj₂ (nodes-offer-BD (toSys r) blkA off))
        (noOffer→viewV _ (medium-api-non-offer (med (toSys r)) aicBF)))

-- … the CD-leg mirror
whole-offer-CD : (r : RState)
  → IoOffers (absNodeD (nD (toSys r))) (apiBF linkCD hi recvBFBlock) blkA
  → IoOffers (radec r ∖ hidden blkA) (apiBF linkCD hi recvBFBlock) blkA
whole-offer-CD r off =
    _
  , ∖-ev (hidden blkA) (radec r) ¬hidden-CD
      (lift-nodes-whole-ev (decMed (med (toSys r))) _ (λ ())
        (proj₂ (nodes-offer-CD (toSys r) blkA off))
        (noOffer→viewV _ (medium-api-non-offer (med (toSys r)) aicBF)))

-- *** THE PARKED OFFER, leg BD ***  `AtPos legBD lpDnClient blkA` — the token in
-- D's BF client carrying `blkA`, D's driver at `cp3` — makes the kept BD receive
-- of `blkA` an OFFER of the hidden abstraction.  Note which two of `AtPos`'s
-- four conjuncts are used: the client position and the consumer phase; the two
-- upstream driver facts (`ProdSent`, `RelayFwd`) are NOT needed for the offer.
parkedOffer-BD : (r : RState) → AtPos legBD lpDnClient blkA (toSys r)
               → IoOffers (radec r ∖ hidden blkA) (apiBF linkBD hi recvBFBlock) blkA
parkedOffer-BD r (hcli , _ , _ , hph) =
  whole-offer-BD r
    (nodeD-offer-BD (nD (toSys r)) blkA (cblk (consOf legBD (toSys r))) hcli
       (consCp3⇒form (consOf legBD (toSys r)) hph))

-- *** THE PARKED OFFER, leg CD ***  the mirror
parkedOffer-CD : (r : RState) → AtPos legCD lpDnClient blkA (toSys r)
               → IoOffers (radec r ∖ hidden blkA) (apiBF linkCD hi recvBFBlock) blkA
parkedOffer-CD r (hcli , _ , _ , hph) =
  whole-offer-CD r
    (nodeD-offer-CD (nD (toSys r)) blkA (cblk (consOf legCD (toSys r))) hcli
       (consCp3⇒form (consOf legCD (toSys r)) hph))

------------------------------------------------------------------------
-- §7  O7 — THE MENU TRANSPORT, and the DISCHARGE of `DelivObl`.
--
-- `DelivObl` quantifies over an ARBITRARY event index `(X , ee)` and value `a`
-- with `delivMenu … (X , ee) a ≡ just t′`, so the last step transports the two
-- concrete offers of §6 to that index.  The recorded trap (a bare `refl` on the
-- label gets stuck, because the two `evLabel`s carry DIFFERENT carrier types) is
-- avoided by NOT inverting into an existential: `outputHit` takes the offer AT
-- THE OUTPUT'S OWN (event, value) and returns it AT the hit index, so the
-- carrier transport is performed by the `yes refl` pattern of the very decision
-- `Output-cont` itself scrutinises — never by a hand-written classifier.  It is
-- stated GENERICALLY in the carrier `A` and its `DecEq` instance, so unification
-- with `delivMenu`'s own elaboration fixes both and no instance is re-guessed.
------------------------------------------------------------------------

-- a hit of a menu UNION is a hit of the left menu or of the right one
⊕v-inv : (v₁ v₂ : SpecMenu) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X}
         {t′ : SpecProc}
       → (v₁ ⊕v v₂) (X , ee) a ≡ just t′
       → (Σ[ t ∈ SpecProc ] (v₁ (X , ee) a ≡ just t)) ⊎ (v₂ (X , ee) a ≡ just t′)
⊕v-inv v₁ v₂ {X} {ee} {a} with v₁ (X , ee) a
... | just t  = λ _ → inj₁ (t , refl)
... | nothing = λ h → inj₂ h

-- O7  transport an offer of an `Output`'s OWN (event, value) to whatever hit its
-- menu: `Output-cont` fires at exactly ONE index and exactly ONE value, and both
-- facts arrive as the two `yes refl`s below
outputHit : {A : Set 0ℓ} ⦃ _ : DecEq A ⦄ (e : Net_Api Payload A) (v : A)
            (Q : SpecProc) (P : NetProc)
            (X : Set 0ℓ) (ee : Net_Api Payload X) (a : X) {t′ : SpecProc}
          → IoOffers P e v
          → Output-cont e v Q (X , ee) a ≡ just t′
          → IoOffers P ee a
outputHit {A} e v Q P X ee a off with Net_Api-≟ {Payload} (A , e) (X , ee)
... | no  _    = λ ()
... | yes refl with a ≟ v
...   | no  _    = λ ()
...   | yes refl = λ _ → off

-- ONE SIDE of the delivery menu, gated by that leg's `pᵢ ∧ gᵢ`: gate down, the
-- side is `∅v` and there is nothing to prove; gate up, it is the leg's `Output`
sideHit : (l : Link) (bg : Bool) (P : NetProc)
          {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X} {t′ : SpecProc}
        → (bg ≡ true → IoOffers P (apiBF l hi recvBFBlock) blkA)
        → (if bg then Output-cont (apiBF l hi recvBFBlock) blkA (Done blkA) else ∅v)
            (X , ee) a ≡ just t′
        → IoOffers P ee a
sideHit l true  P {X} {ee} {a} h eq =
  outputHit (apiBF l hi recvBFBlock) blkA (Done blkA) P X ee a (h refl) eq
sideHit l false P h ()

-- *** THE DELIVERABLE ***  at a config whose OBLIGATED legs are PARKED AT D,
-- instalment 1's residual `DelivObl` is a THEOREM.  The two premises are
-- per-leg and CONDITIONAL on that leg's own gate — which is the honest shape:
-- `delivMenu` asks for the BD receive only when `p1 ∧ g1`, so only an obligated
-- leg has to be parked.  Nothing here is premised on the OTHER leg.
delivObl-parked : (r : RState) (p1 g1 p2 g2 : Bool)
  → (p1 ∧ g1 ≡ true → AtPos legBD lpDnClient blkA (toSys r))
  → (p2 ∧ g2 ≡ true → AtPos legCD lpDnClient blkA (toSys r))
  → DelivObl p1 g1 p2 g2 (radec r ∖ hidden blkA)
delivObl-parked r p1 g1 p2 g2 hBD hCD eq
  with ⊕v-inv (if p1 ∧ g1 then Output-cont (apiBF linkBD hi recvBFBlock) blkA (Done blkA) else ∅v)
              (if p2 ∧ g2 then Output-cont (apiBF linkCD hi recvBFBlock) blkA (Done blkA) else ∅v)
              eq
... | inj₁ (t , h1) =
  sideHit linkBD (p1 ∧ g1) (radec r ∖ hidden blkA) (λ e → parkedOffer-BD r (hBD e)) h1
... | inj₂ h2       =
  sideHit linkCD (p2 ∧ g2) (radec r ∖ hidden blkA) (λ e → parkedOffer-CD r (hCD e)) h2

-- *** THE `stabR` OBLIGATION AT A PARKED CONFIG ***  the whole of `stabR`,
-- premised ONLY on "every obligated leg is parked at D at `blkA`".  The idle and
-- discharged positions were already free (instalment 1's §3); the produced
-- position is now free too WHENEVER the tokens are parked.
--
-- Each premise MAY USE the `isStable` witness (instalment-3 fix): `StabOffer`'s
-- own antecedent is handed to it, which is what the progress half needs and what
-- the shape at `5ce4357` silently withheld.
stabOffer-parked : (r : RState)
  → (isStable (radec r ∖ hidden blkA) → (q1 q2 q3 q4 : Bool)
       → specPos r ≡ posProd q1 q2 q3 q4
       → q1 ∧ q2 ≡ true → AtPos legBD lpDnClient blkA (toSys r))
  → (isStable (radec r ∖ hidden blkA) → (q1 q2 q3 q4 : Bool)
       → specPos r ≡ posProd q1 q2 q3 q4
       → q3 ∧ q4 ≡ true → AtPos legCD lpDnClient blkA (toSys r))
  → StabOffer r
stabOffer-parked r hBD hCD =
  stabOffer r (λ st q1 q2 q3 q4 eq →
    delivObl-parked r q1 q2 q3 q4 (hBD st q1 q2 q3 q4 eq) (hCD st q1 q2 q3 q4 eq))

------------------------------------------------------------------------
-- §9  *** THE BLOCK PIN, AND THE BRIDGE FROM THE WIDENED JOINT INVARIANT ***
-- (package (2): F2/G5 + assembly G4).
--
-- §5's `stabOffer-parked` asks for the parked position AT `blkA`, and instalment
-- 1's window readers ask for `PipeVal` (`:435`, `:463`).  `LegInv` cannot supply
-- the block: it binds it EXISTENTIALLY, and the four token-hop lemmas all RETURN
-- `LegInv l s′`, so the identity with the source block is re-hidden at every hop.
-- The cheap route the review asked to try — reading `b ≡ blkA` off value-tightness
-- WITHOUT carrying the component — is therefore impossible: value-tightness is an
-- INVARIANT (`PipeValInv:20-31` records why the payload facts must be POSITIVE and
-- new), so it has to ride the fold.  `LiveLegAssembly`'s §6b/§9 does exactly that:
-- `LegJointB` = both legs × (`PipeInvS` × `LegInv` × `TokenExcl` × `PipeVal`),
-- transported by `legJointB-step` at the SAME premise as before (`cellCp3` — which
-- the cellCp3 window discharged, so the transport is premise-free).
--
-- WHAT IS PRODUCED HERE AND WHAT IS STILL ASSUMED, exactly.  The `blkA` premises
-- of §5 are now PRODUCED from the carried object.  What stays assumed is the
-- POSITION — "an obligated leg is parked at D at SOME block" — which is package
-- (3)'s (R3′'s) obligation and nothing else: the residual premise below is
-- `Parked`, a block-FREE statement, so the progress half no longer has to say
-- anything about payloads.
------------------------------------------------------------------------

-- the parked position with the block left OPEN: the block-free shape the progress
-- half (package (3)) has to produce
Parked : TwoLegs → RState → Set
Parked l r = Σ[ b ∈ Block₃ ] AtPos l lpDnClient b (toSys r)

-- *** THE BLOCK PIN (F2/G5) ***  the block parked in D's BF client IS the block
-- the SPEC names.  `AtPos`'s own first conjunct is `CliHas⁺ b (dnClient l s)`,
-- i.e. `dnClient l s ≡ bcBlk1 b` (`LiveLegInv:349-350`), which is exactly the
-- equation `PipeVal`'s clause (7) cashes out (`pipeVal⇒client`,
-- `PipeValInv:214-216`) — so the payload is pinned by the CLIENT slot, the same
-- slot instalment 2's M4 mutation showed pins the offered VALUE.
parked-pin : (l : TwoLegs) (r : RState)
           → PipeVal l (toSys r) → Parked l r
           → AtPos l lpDnClient blkA (toSys r)
parked-pin l r pv (b , at) =
  subst (λ z → AtPos l lpDnClient z (toSys r))
        (pipeVal⇒client l (toSys r) pv (proj₁ at)) at

-- `stabR` at a parked config from the PIN: §5's theorem with its two `blkA`
-- premises discharged, so the caller owes only the block-free `Parked` — and owes
-- it WITH the `isStable` witness in hand (the threaded shape; package (3)'s
-- progress argument consumes exactly that witness)
stabOffer-from-pin : (r : RState)
  → PipeVal legBD (toSys r) → PipeVal legCD (toSys r)
  → (isStable (radec r ∖ hidden blkA) → (q1 q2 q3 q4 : Bool)
       → specPos r ≡ posProd q1 q2 q3 q4 → q1 ∧ q2 ≡ true → Parked legBD r)
  → (isStable (radec r ∖ hidden blkA) → (q1 q2 q3 q4 : Bool)
       → specPos r ≡ posProd q1 q2 q3 q4 → q3 ∧ q4 ≡ true → Parked legCD r)
  → StabOffer r
stabOffer-from-pin r pvB pvC hBD hCD =
  stabOffer-parked r
    (λ st q1 q2 q3 q4 eq g → parked-pin legBD r pvB (hBD st q1 q2 q3 q4 eq g))
    (λ st q1 q2 q3 q4 eq g → parked-pin legCD r pvC (hCD st q1 q2 q3 q4 eq g))

-- *** THE BRIDGE ***  `stabR` at a parked config, fed by the CARRIED object
-- itself: `LegJointB` hands over both legs' value halves by projection (its leg
-- index is ignored, hence `legBD`), so an FSim `Rel` carrying
-- `LegJointB legBD (toSys r)` owes this theorem NOTHING about blocks — only the
-- position, which is package (3), and it owes that WITH `StabOffer`'s own
-- `isStable` witness handed to it.
stabOffer-from-joint : (r : RState)
  → LA.LegJointB legBD (toSys r)
  → (isStable (radec r ∖ hidden blkA) → (q1 q2 q3 q4 : Bool)
       → specPos r ≡ posProd q1 q2 q3 q4 → q1 ∧ q2 ≡ true → Parked legBD r)
  → (isStable (radec r ∖ hidden blkA) → (q1 q2 q3 q4 : Bool)
       → specPos r ≡ posProd q1 q2 q3 q4 → q3 ∧ q4 ≡ true → Parked legCD r)
  → StabOffer r
stabOffer-from-joint r j hBD hCD =
  stabOffer-from-pin r (proj₁ (proj₂ (j legBD))) (proj₁ (proj₂ (j legCD))) hBD hCD

------------------------------------------------------------------------
-- §10  *** THE PROGRESS HALF (package (3), R3′): AN ENABLED HIDDEN MOVE
-- REFUTES AN IN-FLIGHT POSITION. ***
--
-- THE SHAPE OF THE ARGUMENT.  `Parked` is the ONE residual of §9, and the way to
-- get it is: the obligated window puts the token in one of the EIGHT in-flight
-- slots (§2's `window⇒token`, but the dispatch below goes over `LegInv` DIRECTLY
-- because `TokenSomewhere` forgets the driver conjuncts an enabled move needs);
-- `lpDnClient` IS `Parked`; and each of the OTHER seven slots is refuted by
-- exhibiting a HIDDEN MOVE of `radec r ∖ hidden blkA`, which a stable state
-- cannot perform (`Semantics.Stability.stable-no-τ`).
--
-- THE HIDE ARITHMETIC (three levels, re-derived at the point of use):
--   `radec r` IS `(decMed (med (toSys r)) ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES`
--   (`SysReach.radec` = `SysStep.absDec`, both `refl`).  So a move of the whole
--   `radec r ∖ hidden blkA` is built in three steps:
--     (i)   the node-internal step (an `apiES` SYNC of a peer bundle with its
--           driver, or a solo io step);
--     (ii)  the four-node `⦀` lift + the io gate: an api event is NOT in `ioES`,
--           so it goes SOLO past the medium (`medium-api-non-offer`) and the
--           FIRST hide KEEPS it (`lift-nodes-whole-ev`);
--     (iii) the SECOND hide turns it into a τ iff it is in `hidden blkA`
--           (`TLH.Hide-hidden`) — and every api event except A's produce of
--           `blkA` and D's receive of `blkA` is hidden (`Spec.keptB`).
--   An io event (`input`/`output`) is instead hidden by the FIRST hide, as a
--   medium⊗nodes SYNC (`SysStep.lift-io-sync-whole-τ`), and then rides the second
--   hide as a τ; that route needs a medium-side INTRO, which is where the
--   remaining six arms sit (see the interface note at §11).
------------------------------------------------------------------------

-- THE REFUTATION KIT: a HIDDEN visible move of the abstract decode is a τ of the
-- doubly-hidden tree, and a stable state performs no τ.  This is the ONLY place
-- the `isStable` witness threaded by the instalment-3 fix is consumed.
hiddenMove-⊥ : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X}
             → mem (hidden blkA) (X , ee) a
             → IoOffers (radec r) ee a
             → isStable (radec r ∖ hidden blkA) → ⊥
hiddenMove-⊥ r hid (M , st) sta =
  stable-no-τ sta (TLH.Hide-hidden (hidden blkA) (radec r) hid st)

-- an api CS/BF move of the NODES alone is a visible move of `radec r`: it goes
-- solo past the medium (which fires no api at all) and the io hide keeps it.
-- This is `whole-offer-BD`'s inner half, stated GENERICALLY in the event so both
-- the kept receive and the hidden ones use it.
apiNodes-whole : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X}
  → IsApiCSBF ee → (ioES .mem (X , ee) a → ⊥)
  → IoOffers (absNodeA (nA (toSys r)) ⦀ (absNodeB (nB (toSys r))
                ⦀ (absNodeC (nC (toSys r)) ⦀ absNodeD (nD (toSys r))))) ee a
  → IoOffers (radec r) ee a
apiNodes-whole r aic ¬io (N , st) =
    _
  , lift-nodes-whole-ev (decMed (med (toSys r))) _ ¬io st
      (noOffer→viewV _ (medium-api-non-offer (med (toSys r)) aic))

-- a relay driver pinned at `cp3` IS the `cp3` consume driver at its own recorded
-- block (the η `RelayCp3` needs before `subst` can retarget `decCP`; the mirror
-- of §5's `consCp3⇒form`, over `CPPh`'s eight relevant shapes)
relayCp3⇒form : (x : CPPh) → RelayCp3 x → x ≡ consuming (relayBlk x) cp3
relayCp3⇒form (consuming b cp0) ()
relayCp3⇒form (consuming b cp1) ()
relayCp3⇒form (consuming b cp2) ()
relayCp3⇒form (consuming b cp3) _ = refl
relayCp3⇒form (consuming b cp4) ()
relayCp3⇒form (consuming b cp5) ()
relayCp3⇒form (consuming b cp6) ()
relayCp3⇒form (producing b pp)  ()

-- THE RELAY DRIVER's offer of the up-link receive at `cp3`: the SAME `decCons`
-- step §5 used at node D, propagated through the relay's OWN bind continuation
-- (`>>= λ b′ → produce l₂ hi b′` in place of `>> Skip` — `TLB.bind-ev` is generic
-- in the continuation, which is why nothing here duplicates `consD-offer-recv`)
relay-offer-recv : (l₁ l₂ : Link) (b₀ x : Block₃)
                 → IoOffers (decCP l₁ l₂ (consuming b₀ cp3)) (apiBF l₁ hi recvBFBlock) x
relay-offer-recv l₁ l₂ b₀ x =
    _
  , TLB.bind-ev (λ b′ → produce l₂ hi b′) (decCons l₁ hi b₀ cp3)
      (sVis refl (consVis-cp3 l₁ b₀ x))

-- NODE B (leg BD's relay): the up-link BF client's api receive SYNCS with the
-- relay driver parked at `cp3`.  BOTH operands are pinned by `AtPos legBD
-- lpUpClient`: its first conjunct is the client slot, its THIRD is `RelayCp3` —
-- which is exactly why this position needs no co-position invariant.
nodeB-relay-recv : (nb : SN.NodeStateB) (b b₀ : Block₃)
  → SN.NodeStateB.bfC-AB nb ≡ bcBlk1 b
  → SN.NodeStateB.cp-B nb ≡ consuming b₀ cp3
  → IoOffers (absNodeB nb) (apiBF linkAB hi recvBFBlock) b
nodeB-relay-recv nb b b₀ hcli hcp =
    _
  , lift-api-node-ev _ _ tt
      (⦀-ev-L _ _ (proj₂ bOff)
        (noOffer→viewV _
          (absBundleG-api-no linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb)
             (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb)
             ahlBF linkAB≢linkBD tt)))
      (proj₂ dOff)
  where
  -- the AB bundle offers the receive at the client position the invariant names
  -- (node B's AB peers are clients on `hi`, so `bundle-offer-recv`'s `(cl, sv)`
  -- instance is `(hi, lo)` — the SAME instance node D used on its down links)
  bOff : IoOffers (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
                     (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
                  (apiBF linkAB hi recvBFBlock) b
  bOff = subst (λ q → IoOffers (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb)
                                  (SN.NodeStateB.csS-AB nb) q (SN.NodeStateB.bfS-AB nb)
                                  (SN.NodeStateB.inert-AB nb))
                               (apiBF linkAB hi recvBFBlock) b)
               (sym hcli)
               (bundle-offer-recv linkAB hi lo (λ ()) (SN.NodeStateB.csC-AB nb)
                  (SN.NodeStateB.csS-AB nb) b (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb))
  -- … and so does the relay driver, at the phase `RelayCp3` pins
  dOff : IoOffers (decCP linkAB linkBD (SN.NodeStateB.cp-B nb)) (apiBF linkAB hi recvBFBlock) b
  dOff = subst (λ q → IoOffers (decCP linkAB linkBD q) (apiBF linkAB hi recvBFBlock) b)
               (sym hcp) (relay-offer-recv linkAB linkBD b₀ b)

-- NODE C (leg CD's relay): the mirror on linkAC/linkCD
nodeC-relay-recv : (nc : SN.NodeStateC) (b b₀ : Block₃)
  → SN.NodeStateC.bfC-AC nc ≡ bcBlk1 b
  → SN.NodeStateC.cp-C nc ≡ consuming b₀ cp3
  → IoOffers (absNodeC nc) (apiBF linkAC hi recvBFBlock) b
nodeC-relay-recv nc b b₀ hcli hcp =
    _
  , lift-api-node-ev _ _ tt
      (⦀-ev-L _ _ (proj₂ bOff)
        (noOffer→viewV _
          (absBundleG-api-no linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc)
             (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc)
             ahlBF linkAC≢linkCD tt)))
      (proj₂ dOff)
  where
  -- the AC bundle's offer at the invariant's client position
  bOff : IoOffers (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
                     (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
                  (apiBF linkAC hi recvBFBlock) b
  bOff = subst (λ q → IoOffers (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc)
                                  (SN.NodeStateC.csS-AC nc) q (SN.NodeStateC.bfS-AC nc)
                                  (SN.NodeStateC.inert-AC nc))
                               (apiBF linkAC hi recvBFBlock) b)
               (sym hcli)
               (bundle-offer-recv linkAC hi lo (λ ()) (SN.NodeStateC.csC-AC nc)
                  (SN.NodeStateC.csS-AC nc) b (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc))
  -- … and the relay driver's, at `cp3`
  dOff : IoOffers (decCP linkAC linkCD (SN.NodeStateC.cp-C nc)) (apiBF linkAC hi recvBFBlock) b
  dOff = subst (λ q → IoOffers (decCP linkAC linkCD q) (apiBF linkAC hi recvBFBlock) b)
               (sym hcp) (relay-offer-recv linkAC linkCD b₀ b)

-- the FOUR-NODE lift when node B fires: B is the SECOND operand, so one
-- `⦀-ev-R` past A and one `⦀-ev-L` inside the tail, with C and D refuted by the
-- same fingerprint (`absNode{A,C,D}-no-when-B`, the banked 12-way family)
nodes-offer-B : (s : SysState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X}
  → apiES .mem (X , ee) a
  → (ApiIsCons ee × ApiHasLink linkAB ee) ⊎ (ApiIsProd ee × ApiHasLink linkBD ee)
  → IoOffers (absNodeB (nB s)) ee a
  → IoOffers (absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) ee a
nodes-offer-B s am fp (M , st) =
    _
  , ⦀-ev-R _ _
      (⦀-ev-L _ _ st
        (noOffer→viewV _
          (⦀-noOffer _ _ (absNodeC-no-when-B (nC s) am fp)
                         (absNodeD-no-when-B (nD s) am fp))))
      (noOffer→viewV _ (absNodeA-no-when-B (nA s) am fp))

-- … and when node C fires (THIRD operand: two `⦀-ev-R`s then `⦀-ev-L`)
nodes-offer-C : (s : SysState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X}
  → apiES .mem (X , ee) a
  → (ApiIsCons ee × ApiHasLink linkAC ee) ⊎ (ApiIsProd ee × ApiHasLink linkCD ee)
  → IoOffers (absNodeC (nC s)) ee a
  → IoOffers (absNodeA (nA s) ⦀ (absNodeB (nB s) ⦀ (absNodeC (nC s) ⦀ absNodeD (nD s)))) ee a
nodes-offer-C s am fp (M , st) =
    _
  , ⦀-ev-R _ _
      (⦀-ev-R _ _
        (⦀-ev-L _ _ st (noOffer→viewV _ (absNodeD-no-when-C (nD s) am fp)))
        (noOffer→viewV _ (absNodeB-no-when-C (nB s) am fp)))
      (noOffer→viewV _ (absNodeA-no-when-C (nA s) am fp))

-- the RELAY's receive is HIDDEN, and this is where the `∖ hidden blkA` side
-- condition FLIPS relative to §5: `keptB`'s receive clause admits only the DOWN
-- links (`⌊ l ≟ linkBD ⌋ ∨ ⌊ l ≟ linkCD ⌋`), so on an UP link it is `false`
-- whatever the carried block — the FIRST conjunct already decides it, which is
-- why this needs no `blkA-refl` and holds for the existential block
hidden-upRecv-AB : (x : Block₃) → mem (hidden blkA) (Block₃ , apiBF linkAB hi recvBFBlock) x
hidden-upRecv-AB x = refl

-- … the AC mirror
hidden-upRecv-AC : (x : Block₃) → mem (hidden blkA) (Block₃ , apiBF linkAC hi recvBFBlock) x
hidden-upRecv-AC x = refl

-- *** THE PER-POSITION OBLIGATION OF THE PROGRESS HALF ***  "a STABLE config is
-- not at this position, carrying THIS block": the block-indexed form, which is
-- the one a PREMISE should take (see `Refuted` below).
RefutedAt : TwoLegs → LegPos → Block₃ → RState → Set₁
RefutedAt l k b r = AtPos l k b (toSys r)
                  → isStable (radec r ∖ hidden blkA) → ⊥

-- the BLOCK-AGNOSTIC form, for the arms that are THEOREMS: a proof is worth more
-- at every block, and §10's ladder is block-agnostic anyway (the M4 note explains
-- why: hidden-ness of the relay's receive never consults the block).  Premises go
-- at `RefutedAt … blkA` instead — quantifying a PREMISE over `b` would assume
-- strictly more than any consumer can use, since `PipeVal` pins every occupied
-- slot's payload to `blkA` at the dispatch (`pinAt*` below).
Refuted : TwoLegs → LegPos → RState → Set₁
Refuted l k r = (b : Block₃) → RefutedAt l k b r

-- *** ARM `lpUpClient`, leg BD — DISCHARGED. ***  The token in the relay's up BF
-- client is an ENABLED HIDDEN MOVE: the client offers `apiBF linkAB hi
-- recvBFBlock · b` (§5's `bfc-offer-recv`, lifted by `bundle-offer-recv`), the
-- relay driver at `cp3` offers the same event, `apiES` makes them SYNC, the three
-- sibling nodes and the medium refuse, and `∖ hidden blkA` turns the survivor into
-- a τ — which contradicts stability.  NOTE WHICH CONJUNCTS PAY: the client slot
-- (first) and `RelayCp3` (third); `ProdSent` and `InCp03` are not used.
noUpClient-BD : (r : RState) → Refuted legBD lpUpClient r
noUpClient-BD r b (hcli , _ , hr3 , _) =
  hiddenMove-⊥ r (hidden-upRecv-AB b)
    (apiNodes-whole r aicBF (λ ())
      (nodes-offer-B (toSys r) tt (inj₁ (aicBFrecv , ahlBF))
        (nodeB-relay-recv (nB (toSys r)) b (relayBlk (relayOf legBD (toSys r))) hcli
           (relayCp3⇒form (relayOf legBD (toSys r)) hr3))))

-- *** ARM `lpUpClient`, leg CD — DISCHARGED. ***  the node-C mirror
noUpClient-CD : (r : RState) → Refuted legCD lpUpClient r
noUpClient-CD r b (hcli , _ , hr3 , _) =
  hiddenMove-⊥ r (hidden-upRecv-AC b)
    (apiNodes-whole r aicBF (λ ())
      (nodes-offer-C (toSys r) tt (inj₁ (aicBFrecv , ahlBF))
        (nodeC-relay-recv (nC (toSys r)) b (relayBlk (relayOf legCD (toSys r))) hcli
           (relayCp3⇒form (relayOf legCD (toSys r)) hr3))))

------------------------------------------------------------------------
-- §11  *** THE POSITION DISPATCH, AND `stabR` AS A THEOREM. ***
--
-- The whole progress half is a ten-way split of `LegInv l s = Σ[ b ] Σ[ k ] AtPos
-- l k b s`.  The dispatch is over `LegPos` DIRECTLY, not over §2's
-- `TokenSomewhere`: the disjunction is a BARE OCCUPANCY fact by design
-- (`LiveLegInv`'s non-vacuity guard), and every enabled-move construction needs
-- the driver conjuncts that `AtPos` carries beside the occupied slot — the
-- `lpUpClient` arm above is precisely a case in point (`RelayCp3` is its second
-- operand).  So `window⇒token` is NOT on the path from here; the window is used
-- only for its two component facts, which kill `lpPreSend` and `lpDone`.
--
-- *** WHAT IS OPEN AND WHY, exactly (the R3′ finding, machine-checkable). ***
-- Six of the eight in-flight positions remain, as the record below, and they
-- split into two families with DIFFERENT missing ingredients:
--
--   (a) THE SERVER AND CELL POSITIONS (`lpUpSrv`/`lpDnSrv`, `lpUpCell`/
--       `lpDnCell`) fire an *io* move, and `input`/`output` are NOT in `apiES`
--       (`FourNodeDiamond.apiSet-dec` answers `no` on both) while they ARE in
--       `ioES` (`NetCommon.ioSet-dec`).  Two consequences, both verified from
--       those definitions: the move goes SOLO past the node's own `∥⇘ apiES ⇙`
--       gate — so the DRIVER is not an operand — and it is hidden by the FIRST
--       hide, as a medium⊗nodes SYNC (`SysStep.lift-io-sync-whole-τ`, which
--       demands BOTH operand steps).
--       *** Hence the charter's cheap route is DEAD, for a reason that is a
--       component mismatch and not a matter of price: `cellCp3` pins the reader's
--       DRIVER (`RelayCp3 (relayOf l s)` on the up cell, `ConsCp3 (phOf l s)` on
--       the down cell — `LiveLegStep.CellCp3`), and the io sync needs the reader's
--       BF CLIENT PEER (`upClient`/`dnClient` at a `MsgBlock`-accepting position).
--       Those are different components of the state, and no invariant in the
--       campaign relates them. *** The same gap, in its other orientation, blocks
--       the server positions: `bsBlk1 b` fires `input … ! MsgBlock b`
--       (`SysNode.decBFs-src`, `bsBlk1` row), which needs the cell EMPTY, and when
--       the cell instead holds an unread `MsgStartBatch` the enabled move is the
--       far client's drain — the gate verdict's H19 row.  `TokenExcl` cannot
--       close it either: a `MsgStartBatch` in the cell is not a token.
--       SECOND, INDEPENDENT ITEM for this family: the medium-side INTRO.
--       `SysOracle_NodeTauEv.offer-{full,empty}` (`:1007-1017`) ARE rung 1 of it,
--       in the INTRO direction — the funding review had that right; what is
--       missing is only the lift from one cell to `decMed`, i.e. the `decCopy →
--       ⦀⋆ (12 cells) → decLink (△) → ⦀Fin (4 links) → renameMap` ladder, whose
--       existing occupants (`PipeMedKey.cell{-in,-out,Flip}-key`, `⦀Fin-ev-inv`)
--       all run in the INVERSION direction.  `WalkBrkFire.medium-break-fire`
--       (`:199-241`) is the shape it must take, one channel simpler (a break needs
--       no cell fold).  SMALL — the report prices it at ~80-150, since only the
--       12-cell `⦀⋆` rung is genuinely new.  It is NOT built here because it would
--       close no arm on its own (the peer position is still missing), so it could
--       be neither exercised nor falsification-tested.
--   (b) THE RELAY-DRIVER POSITIONS (`lpRelayIn` = `consuming _ cp4..cp6`,
--       `lpRelayOut` = `producing _ pp0..pp5`) fire an *api* move, so the ladder
--       of §10 applies verbatim — but the co-operand is the relay's own CS/BF
--       PEER, whose position `AtPos` does not carry (verdict rows H0-H17,
--       H22-H23: `cp4` needs the up BF CLIENT at `bcIdle`; `pp0` fires
--       `reqCSRequestNext`, which is a SERVER-side callback, so it needs the down
--       CS SERVER at `ssReqNext1` — `SysNode.agda:325` and its decode `:337-339`
--       — NOT a client position; …).  This is the handshake-ladder co-position
--       family, and unlike (a) it needs no new machinery at all — only the
--       invariant content.  Note the WIDTH: nine sub-phase co-parties across four
--       component classes, and `CScPos`/`CSsPos` are named by NO invariant the
--       campaign carries, so this family is TokenExcl-scale, not a ladder.
--
-- Both families are therefore `LegInv`-level invariant content with its own
-- preservation across all sixteen step classes, which is the Task-3-scale object
-- the instalment-1 re-derivation priced as R2 and the funding review deferred.
--
-- *** THE RIGHT TEMPLATE FOR WHOEVER FUNDS THE COMPLETION ***
-- `LiveTokenExcl.agda:255-262` already PARKS two statements of exactly the
-- "occupied slot ⇒ co-party position" shape (`UpChainCp3`, `DnChainCp3`,
-- unproved, depended on by nothing).  They name the WRONG component for the six
-- arms here — the reader's DRIVER, not its peer — but the shape, the placement
-- and the "nothing depends on them" discipline are the template.  And note the
-- deeper reading (gate verdict §7): the six open arms are the price of `LegPos`
-- being a TEN-constructor coarsening of a ~24-position hop table, so the
-- structurally correct alternative to funding six co-position families is
-- REFINING `LegPos` — which must be priced before either is chosen.
-- NOTHING below is premised on anything else: the six fields are the ONLY
-- residual, they are stated over STATE facts (never "something is enabled"), and
-- each is exactly the type the discharged `noUpClient-*` arms have.
------------------------------------------------------------------------

-- THE SIX BLOCK PINS.  `PipeVal`'s eight clauses pin every occupied slot's
-- payload to `blkA`, and each in-flight `AtPos` clause hands over an EQUATION on
-- exactly that slot — so one `subst` per position turns the existential block into
-- `blkA`, exactly as §9's `parked-pin` does at `lpDnClient` (this is the same
-- mechanism, applied at the other six slots instead of the parked one).  These
-- exist so the RESIDUAL can be stated at `blkA` alone.

-- a value-correct BF SERVER slot holding `b` holds `blkA` (clauses (1) and (5))
pinSrv : (bfs : BFsPos) (b : Block₃) → SrvValOK bfs → bfs ≡ bsBlk1 b → b ≡ blkA
pinSrv bfs b h eq = subst SrvValOK eq h

-- … a value-correct CELL holding the `MsgBlock b` payload (clauses (2) and (6)):
-- `CellValOK (full (blkPayload b))` IS `MsgValOK (blockFetch (MsgBlock b))`
pinCell : (ph : CopyPhase) (b : Block₃)
        → CellValOK ph → ph ≡ full (blkPayload b) → b ≡ blkA
pinCell ph b h eq = subst CellValOK eq h

-- (NO client pin: `lpUpClient` is PROVED at every block and `lpDnClient` IS the
-- existential goal, so clauses (3) and (7) are not read here — §9's `parked-pin`
-- is clause (7)'s consumer.)

-- the RELAY's recorded block on its CONSUME tail is `blkA`: `RelayIn` pins the
-- phase into `ConsValAt`'s constrained region (`cp4..cp6`), where the clause IS
-- the equation (clause (4), consume arm)
pinRelayIn : (x : CPPh) → RelayValOK x → RelayIn x → relayBlk x ≡ blkA
pinRelayIn (consuming b cp0) _ ()
pinRelayIn (consuming b cp1) _ ()
pinRelayIn (consuming b cp2) _ ()
pinRelayIn (consuming b cp3) _ ()
pinRelayIn (consuming b cp4) h _ = h
pinRelayIn (consuming b cp5) h _ = h
pinRelayIn (consuming b cp6) h _ = h
pinRelayIn (producing b pp)  _ ()

-- … and on its PRODUCE tail, where `RelayValOK` is unconditionally the equation
-- (clause (4), produce arm — a relay only produces what it consumed)
pinRelayOut : (x : CPPh) → RelayValOK x → RelayOut x → relayBlk x ≡ blkA
pinRelayOut (consuming b cp)  _ ()
pinRelayOut (producing b pp)  h _ = h

-- the five `PipeVal` clauses the six open positions read, NAMED (the accessor
-- style §1b's `pipeVal-cons` established, so no consumer repeats six `proj₂`s)
pv1 : (l : TwoLegs) (s : SysState) → PipeVal l s → SrvValOK   (upSrv   l s)
pv1 l s (h , _) = h

pv2 : (l : TwoLegs) (s : SysState) → PipeVal l s → CellValOK  (cellUp  l s)
pv2 l s (_ , h , _) = h

pv4 : (l : TwoLegs) (s : SysState) → PipeVal l s → RelayValOK (relayOf l s)
pv4 l s (_ , _ , _ , h , _) = h

pv5 : (l : TwoLegs) (s : SysState) → PipeVal l s → SrvValOK   (dnSrv   l s)
pv5 l s (_ , _ , _ , _ , h , _) = h

pv6 : (l : TwoLegs) (s : SysState) → PipeVal l s → CellValOK  (cellDn  l s)
pv6 l s (_ , _ , _ , _ , _ , h , _) = h

-- retarget a position along a block equation (the `parked-pin` move, at any `k`)
retarget : (l : TwoLegs) (r : RState) (k : LegPos) {b : Block₃}
         → b ≡ blkA → AtPos l k b (toSys r) → AtPos l k blkA (toSys r)
retarget l r k eq at = subst (λ z → AtPos l k z (toSys r)) eq at

-- THE RESIDUAL, as one record: the six in-flight positions R3′ leaves open, each
-- at the SINGLE block `blkA` (the pins above are what let it be stated this
-- weakly — a `∀ b` premise would assume more than any consumer can use).  The
-- SEVENTH in-flight position, `lpUpClient`, is proved above and supplied by the
-- bridges below, so a successor's job is exactly these six fields — and each is
-- `RefutedAt`-shaped, i.e. an instance of the interface `noUpClient-BD` meets.
-- *** THE FOUR io FIELDS CARRY THE LEG'S OWN LINK-UNBROKENNESS ANTECEDENT, AND
-- THAT IS MANDATORY, NOT STYLISTIC. ***  Every io-class enabled move (the
-- server's wire-send into an empty cell, the reader's delivery out of a full one,
-- the medium's drain τ out of a draining one) is a move OF THE MEDIUM, and a
-- BROKEN link's medium decodes to `Skip`, which offers nothing at all
-- (`SysMedium.decLink`'s broken clause).  So no unconditional form of these four
-- fields is provable — and unbrokenness is NOT invariant-carryable either: a
-- `break` is a VISIBLE event that every preserved conjunct transports across
-- (`PipeEvStep.break-med-phase` keeps the phase function, `evStepB-break`
-- transports `LegJointB`), so no carried object can imply it at a cell or server
-- position.  What DOES supply it is the OBLIGATED WINDOW: `wLink1`/`wLink2`
-- (`:494-495`) are exactly these two facts, and `parked-of` forwards them to the
-- fields below.  (Task-1 report §Concern 2; Task-1 review's machine-checked
-- impossibility.)
-- *** THE TWO api FIELDS CARRY THE DOWN LINK'S ANTECEDENT TOO SINCE THE CROSS-NODE
-- api CAMPAIGN'S T2, AND IT IS THE SAME MANDATORY KIND. ***  They used to need none:
-- their ladders had no medium operand at all.  T2's `pp5` discharge gives them one —
-- the residual's `pp5` equation is `dnSrv ≡ bsStream`, the carried coupling pins the
-- server only to `{bsWsb, bsStream}`, and the `bsWsb` half is closed by exhibiting
-- the server's own wire-send as an enabled hidden τ (`LiveSrvOpen.srvWsb-⊥`).  That
-- is a move OF THE MEDIUM: at a BROKEN down link the ladder has NO move to exhibit,
-- so the `bsWsb` half cannot be closed by this route at all.  *** STATE THE STRENGTH
-- OF THAT EXACTLY, and do not quote it as more. ***  What is CHECKED is the proof's
-- medium-dependence: both arms of `srvWsb-⊥` consume the unbrokenness hypothesis, and
-- F21 (`LiveSrvOpen` §3) is the arity-preserving mutation that shows the leg's OWN
-- link is the one that licenses the move.  What is NOT checked anywhere in this tree
-- is a WITNESS — no state exhibiting a STABLE `(pp5, bsWsb)` at a broken link has been
-- constructed — so "the equation is FALSE there" is an ARGUMENT, not a fact of record;
-- the antecedent is justified by unprovability-as-unguarded, which is the same footing
-- the four io fields' antecedents have always had.  `parked-at` forwards `hb2` to both
-- fields now, exactly as it forwards it to the down cell and the down server.
-- *** (T10) … AND IT FORWARDS `hb1` TO BOTH AS WELL. ***  The `cp4` arm's discharge
-- runs on the UP medium, so the two relay fields' antecedent is now BOTH links; the
-- paragraph above is unchanged for the `pp3` half and for every CS arm.
record InFlightOpen (l : TwoLegs) (r : RState) : Set₁ where
  constructor mkOpen
  field
    oUpSrv    : broken (med (toSys r)) (upLink l) ≡ false
              → RefutedAt l lpUpSrv    blkA r
    oUpCell   : broken (med (toSys r)) (upLink l) ≡ false
              → RefutedAt l lpUpCell   blkA r
    -- *** (T10) THE TWO RELAY FIELDS TAKE **BOTH** LINK FACTS. ***  The `cp4`
    -- discharge is a move of the UP medium (node A's `MsgBatchDone`, and the up
    -- client's own stream read), so the relay arms' refutations now depend on the
    -- leg's up link exactly as the up pair's always have — while their `pp3`
    -- residual and every CS arm still depend on the down one.  `parked-at` holds
    -- both facts already (`hb1`/`hb2`), so the widening costs one argument at each
    -- of the two call sites below and one at each producer.
    oRelayIn  : broken (med (toSys r)) (upLink l) ≡ false
              → broken (med (toSys r)) (dnLink l) ≡ false
              → RefutedAt l lpRelayIn  blkA r
    oRelayOut : broken (med (toSys r)) (upLink l) ≡ false
              → broken (med (toSys r)) (dnLink l) ≡ false
              → RefutedAt l lpRelayOut blkA r
    oDnSrv    : broken (med (toSys r)) (dnLink l) ≡ false
              → RefutedAt l lpDnSrv    blkA r
    oDnCell   : broken (med (toSys r)) (dnLink l) ≡ false
              → RefutedAt l lpDnCell   blkA r
open InFlightOpen public

-- THE TEN-WAY DISPATCH on an EXPLICIT `LegPos` argument (never a `with`, so the
-- `AtPos` premise reduces per clause and the recorded ICE shape is avoided):
-- `lpPreSend` and `lpDone` die on the window's two component facts, `lpDnClient`
-- IS the goal, and the other eight are refuted — one by §10, six by the residual.
-- (the six `subst`s below are the pins in action: the residual is stated at
-- `blkA`, so each open arm is fed the position RETARGETED along its own slot's
-- value clause.  `lpDnClient` needs no pin — `Parked` is existential — and the
-- two excluded positions need none either.)
-- (Task 4) the two link facts are threaded HERE, beside the two window flags
-- `hp`/`hc` that were already threaded, and consumed by exactly the four io arms
-- — the up pair reads `hb1`, the down pair `hb2`, and neither api arm reads
-- either.
parked-at : (l : TwoLegs) (r : RState) (b : Block₃) (k : LegPos)
          → AtPos l k b (toSys r) → PipeVal l (toSys r)
          → ProdSent (prodOf l (toSys r)) → InCp03 (phOf l (toSys r))
          → broken (med (toSys r)) (upLink l) ≡ false
          → broken (med (toSys r)) (dnLink l) ≡ false
          → Refuted l lpUpClient r → InFlightOpen l r
          → isStable (radec r ∖ hidden blkA) → Parked l r
parked-at l r b lpPreSend   at pv hp hc _   _   _   _  _   =
  ⊥-elim (prodSent-notSent-⊥ (prodOf l (toSys r)) hp (proj₁ (proj₂ at)))
parked-at l r b lpUpSrv     at pv _  _  hb1 _   _   op sta =
  ⊥-elim (oUpSrv op hb1
    (retarget l r lpUpSrv
      (pinSrv  (upSrv  l (toSys r)) b (pv1 l (toSys r) pv) (proj₁ at)) at) sta)
parked-at l r b lpUpCell    at pv _  _  hb1 _   _   op sta =
  ⊥-elim (oUpCell op hb1
    (retarget l r lpUpCell
      (pinCell (cellUp l (toSys r)) b (pv2 l (toSys r) pv) (proj₁ at)) at) sta)
parked-at l r b lpUpClient  at pv _  _  _   _   huc _  sta = ⊥-elim (huc b at sta)
parked-at l r b lpRelayIn   at pv _  _  hb1 hb2 _   op sta =
  ⊥-elim (oRelayIn op hb1 hb2
    (retarget l r lpRelayIn
      (trans (sym (proj₂ (proj₁ at)))
             (pinRelayIn  (relayOf l (toSys r)) (pv4 l (toSys r) pv)
                          (proj₁ (proj₁ at)))) at) sta)
parked-at l r b lpRelayOut  at pv _  _  hb1 hb2 _   op sta =
  ⊥-elim (oRelayOut op hb1 hb2
    (retarget l r lpRelayOut
      (trans (sym (proj₂ (proj₁ at)))
             (pinRelayOut (relayOf l (toSys r)) (pv4 l (toSys r) pv)
                          (proj₁ (proj₁ at)))) at) sta)
parked-at l r b lpDnSrv     at pv _  _  _   hb2 _   op sta =
  ⊥-elim (oDnSrv op hb2
    (retarget l r lpDnSrv
      (pinSrv  (dnSrv  l (toSys r)) b (pv5 l (toSys r) pv) (proj₁ at)) at) sta)
parked-at l r b lpDnCell    at pv _  _  _   hb2 _   op sta =
  ⊥-elim (oDnCell op hb2
    (retarget l r lpDnCell
      (pinCell (cellDn l (toSys r)) b (pv6 l (toSys r) pv) (proj₁ at)) at) sta)
parked-at l r b lpDnClient  at pv _  _  _   _   _   _  _   = b , at
parked-at l r b lpDone      at pv hp hc _   _   _   _  _   =
  ⊥-elim (inCp03-recv-⊥ (phOf l (toSys r)) hc (proj₂ (proj₂ (proj₂ at))))

-- *** "STABLE IMPLIES PARKED" ***  the progress half at one leg, off the window:
-- the leg's invariant locates the token, the window's two facts confine it to the
-- eight in-flight slots, and stability refutes seven of them.
-- (Task 4) the window is now taken AT THE LEG'S OWN TWO LINKS (it always was —
-- `window-BD` produces `Window legBD (toSys r) linkAB linkBD` and `upLink legBD`
-- IS `linkAB`), because the two link fields are what the four io fields' new
-- antecedent needs; the generic `{k1 k2}` form could not deliver them.
parked-of : (l : TwoLegs) (r : RState)
          → LegInv l (toSys r) → PipeVal l (toSys r)
          → Window l (toSys r) (upLink l) (dnLink l)
          → Refuted l lpUpClient r → InFlightOpen l r
          → isStable (radec r ∖ hidden blkA) → Parked l r
parked-of l r (b , k , at) pv w huc op sta =
  parked-at l r b k at pv (wSent w) (wPend w) (wLink1 w) (wLink2 w) huc op sta

-- a `true` conjunction has both sides `true` (the `delivMenu` gate arrives as one
-- `qᵢ ∧ qⱼ ≡ true`, while the window readers ask for the two flags separately)
∧-true : (x y : Bool) → x ∧ y ≡ true → (x ≡ true) × (y ≡ true)
∧-true true  true  _ = refl , refl
∧-true true  false ()
∧-true false y     ()

-- LEG BD's `Parked` producer at exactly the type `stabOffer-from-joint` demands:
-- the carried joint object supplies both `LegInv` (component 2 of `LegJoint`) and
-- `PipeVal` (the §9 widening), the spec position supplies the window, and the
-- `isStable` witness supplies the refutations
parked-BD : (r : RState) → LA.LegJointB legBD (toSys r) → InFlightOpen legBD r
          → isStable (radec r ∖ hidden blkA) → (q1 q2 q3 q4 : Bool)
          → specPos r ≡ posProd q1 q2 q3 q4 → q1 ∧ q2 ≡ true → Parked legBD r
parked-BD r j op sta q1 q2 q3 q4 eq g =
  parked-of legBD r (proj₁ (proj₂ (proj₁ (j legBD)))) (proj₁ (proj₂ (j legBD)))
    (window-BD r eq (proj₁ (∧-true q1 q2 g)) (proj₂ (∧-true q1 q2 g)) (proj₁ (proj₂ (j legBD))))
    (noUpClient-BD r) op sta

-- LEG CD's mirror, off `q3 ∧ q4` and the AC/CD links
parked-CD : (r : RState) → LA.LegJointB legBD (toSys r) → InFlightOpen legCD r
          → isStable (radec r ∖ hidden blkA) → (q1 q2 q3 q4 : Bool)
          → specPos r ≡ posProd q1 q2 q3 q4 → q3 ∧ q4 ≡ true → Parked legCD r
parked-CD r j op sta q1 q2 q3 q4 eq g =
  parked-of legCD r (proj₁ (proj₂ (proj₁ (j legCD)))) (proj₁ (proj₂ (j legCD)))
    (window-CD r eq (proj₁ (∧-true q3 q4 g)) (proj₂ (∧-true q3 q4 g)) (proj₁ (proj₂ (j legCD))))
    (noUpClient-CD r) op sta

-- *** THE CAMPAIGN'S CLOSING THEOREM ***  `stabR` at every reachable config, from
-- the CARRIED joint invariant alone plus the six open positions — no block
-- premise, no window premise, no parked premise, and the `isStable` witness
-- consumed where it belongs.  `LegJointB` is transported by
-- `LA.legJointB-step` at the campaign's then-single premise `cellCp3` (discharged at
-- the cellCp3 window: a theorem off the carried join); this theorem
-- itself takes NEITHER (its object is §6b's, deliberately placed outside that
-- parameter), so `stabR` is a theorem from `LegJointB` + `InFlightOpen`.
--
-- *** THE HONESTY COST, STATED PLAINLY — DO NOT QUOTE THIS THEOREM WITHOUT THE
-- TWELVE FACTS IN THE SAME BREATH. ***  Six of the EIGHT in-flight positions are
-- ARGUMENTS of this theorem, per leg: what is PROVED HERE, MODULE-LOCALLY, is the
-- parked position's own offer (§5-§7), the window's two exclusions and one
-- in-flight position out of eight (`lpUpClient`), so the honest local reading is
-- "given that a stable configuration cannot have the token in either server,
-- either cell, or either relay-driver tail, `stabR` holds".
--
-- *** WHAT IS NO LONGER TRUE OF THE TREE (tasks 4 and 5 — read this before quoting
-- the paragraph above as a limitation). ***  EIGHT of those twelve arguments are now
-- PREMISE-FREE THEOREMS, supplied by `LivenessProof.At.ifo-of` (`LivenessProof:432`;
-- the old `:297-314` predated ~340 lines of doc insertion):
-- the four cell positions off `LiveChanInv.cellOpen-up-chan`/`-dn-chan` and the four
-- server positions off `LiveSrvOpen.srvOpen-up`/`-dn`, each taking that hop's own
-- channel invariant (CARRIED, both hops, by `LiveChanJoin` in the FSim's `Rel`), the
-- CARRIED `NoTwoTokens`, and the link fact the fields' antecedent now demands.  The
-- four relay-driver positions ARE THEOREMS OUTRIGHT, and *** THE PREMISED CONTENT OF
-- THE ROUTE IS NOTHING AT ALL. ***  (SUPERSEDED IN PLACE — this sentence was stale by
-- SEVEN discharges plus the window, and was the worst-reading line left in the tree:
-- it said "theorems modulo `LiveRelayCS`'s SEVEN-equation (nine before T1's `pp4` and
-- T2's `pp5` discharges), `isStable`-scoped api residual.  So the premised content of
-- the ROUTE is `cellCp3` plus that residual".  The residual is ZERO — `pp1` T5, `pp2`
-- T6d, `cp5` T7, `cp6`/`pp0` T8c-iii, `cp4` T10, `pp3` T11h, and BOTH fields retired
-- (`csRes` T8c-iii, `bfRes` T12) — and `cellCp3` is a theorem since the cellCp3 window
-- (`LiveChanJoin.cellCp3-of`), so `LivenessProof.At.Premises` is an EMPTY record.)
-- Not twelve position facts, then, and not a residual either — §11's header explains why none of the six was buildable
-- AT THIS LAYER, which is why the route builds them one layer up.
stabR-final : (r : RState) → LA.LegJointB legBD (toSys r)
            → InFlightOpen legBD r → InFlightOpen legCD r → StabOffer r
stabR-final r j opB opC =
  stabOffer-from-joint r j
    (λ st q1 q2 q3 q4 eq g → parked-BD r j opB st q1 q2 q3 q4 eq g)
    (λ st q1 q2 q3 q4 eq g → parked-CD r j opC st q1 q2 q3 q4 eq g)

------------------------------------------------------------------------
-- FALSIFICATION NOTES (arity-preserving mutations, per the campaign rule).
--
-- (1) Swap `ix0` for `ix7` in `settle-prod`'s τ-step: it does NOT break — the
--     `sTau` still typechecks (branch 7 exists) but the settled state changes to
--     `prodBr0 true true true true`, so `settle-prod`'s own `DelivObl p1 g1 p2
--     g2` premise no longer matches its containment argument and THAT is what
--     goes red.  So the test bites, but at the containment, not at the τ — the
--     recorded prediction ("branch 7 still typechecks, so this is not a valid
--     falsification") is CORRECT about the τ step and incomplete about the
--     coupling of the two.
-- (2) Drop the `ConsDValOK` argument of `recvOf-false⇒inCp03` (replace it by a
--     `⊤`): the `cp4`/`cp5`/`cp6` clauses lose their `refl` and no longer
--     reduce, so the module goes red — this is the machine-checked form of the
--     header's "the block is not pinned by `LegJoint`" finding.
-- (3) Weaken `window-BD` to read `q3`/`q4` instead of `q1`/`q2` (the leg swap):
--     `mkPos-prod-p1`'s result type no longer matches `prodOf legBD`, red.
-- (4) Replace `notOr-true` by `∨-false` in `window-BD`'s link fields: red, and
--     it is the one that catches a `gᵢ` polarity slip.
--
-- OFFER-HALF MUTATIONS (all three RUN; §5-§7).
-- (5) `nodeD-offer-BD`'s bundle lift `⦀-ev-L` → `⦀-ev-R`: RED as predicted
--     (`[UnequalTerms] Fin.zero != Fin.suc … of type Fin 2` at the `proj₂ bOff`
--     argument), i.e. the leg↔operand-side mapping inside node D is
--     load-bearing — leg BD is node D's LEFT bundle and LEFT driver.
-- (6) `whole-offer-BD`'s hide side condition `¬hidden-BD` → `¬hidden-CD`:
--     GREEN, and that is a FINDING, not a gap — the two types are
--     DEFINITIONALLY EQUAL (both reduce to `⌊ blkA ≟ blkA ⌋ ≡ false → ⊥`),
--     because `keptB`'s link disjunct holds for BOTH kept links and its
--     link/dir tests are concrete.  No link-swap mutation can ever test the
--     hide condition; only a block-swap can, and there is no other block to
--     swap in.  Recorded so no reviewer reads this as a vacuous side condition.
-- (7) In `nodeD-offer-BD`'s `bOff`, offer the bundle at `b₀` (the DRIVER's
--     stored block) instead of `b` (the CLIENT's held block): RED as predicted
--     (`[UnequalTerms] b₀ != b of type Block₃`).  So the offered VALUE is pinned
--     by the CLIENT (`ceqBFc10`'s value gate), not by the driver — `decCons …
--     cp3` is a bare `Prefix` and offers every value.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- FALSIFICATION NOTE for §9 (arity-preserving; applied, built, reverted
-- byte-identically).
--
-- (M1) In `parked-pin` (`:1073-1078`) feed `pipeVal⇒client` the position's
--      SECOND conjunct (`proj₁ (proj₂ at)`, the `ProdSent` driver fact) in place
--      of its first (the client-slot equation).
--      *** RED as predicted ***: `:1078.41-57: error: [UnequalTerms] ProdSent
--      (prodOf l (RState.sys r)) !=< dnClient l (toSys r) ≡ … bcBlk1 _x_ … when
--      checking that the expression proj₁ (proj₂ at) has type …`, EXIT=42.  So
--      the pin genuinely reads the CLIENT SLOT's occupancy equation — the same
--      slot instalment 2's M4 showed pins the offered VALUE — and not any of the
--      coarse driver facts that travel beside it.  RE-RUN after the instalment-3
--      `isStable` threading (the review's Important): still RED, at the same
--      column, so threading the witness did not weaken the pin.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- FALSIFICATION NOTES for §10-§11 (arity-preserving; ALL FOUR RUN; applied,
-- built, reverted byte-identically — `git status` empty after each).  The cited
-- coordinates are at `38b4125` (the slice-A+B state); this closure hunk shifts
-- §10 by the header insertions above, which is the uniform drift a reviewer
-- should apply.  ONE PER PROOF LAYER, as the campaign rule asks: the sync ladder,
-- the invariant read, the position dispatch, and the hide side condition.
--
-- (M1  the LADDER, `nodeB-relay-recv`)  the AB-bundle lift `⦀-ev-L` → `⦀-ev-R`.
--      *** RED as predicted ***: `:1216.20-30: error: [UnequalTerms]
--      Data.Fin.Base.Fin.zero != Data.Fin.Base.Fin.suc (fromℕ< _) of type Fin
--      (numLinks p) … when checking that the expression proj₂ bOff has type
--      absBundleG linkBD lo hi … ─[ ev (evl (evLabel … (apiBF linkAB hi
--      recvBFBlock) b)) ]─► _`, EXIT=42.  So the LEG↔OPERAND mapping inside the
--      relay node is load-bearing: leg BD's UP link is node B's LEFT bundle
--      (mirroring instalment 2's M1 at node D, where leg BD was also the left).
--
-- (M2  the INVARIANT READ, `noUpClient-BD`)  feed `relayCp3⇒form` the position's
--      SECOND conjunct (`ProdSent`) instead of its THIRD (`RelayCp3`).
--      *** RED as predicted ***: `:1336.53-55: error: [UnequalTerms] (ProdSent
--      (SN.prod-AB (nA (RState.sys r)))) !=< (RelayCp3 (SN.cp-B (nB (RState.sys
--      r)))) when checking that the expression hp has type RelayCp3 (relayOf
--      legBD (toSys r))`, EXIT=42.  So the arm genuinely consumes the RELAY PIN —
--      the conjunct that makes this position, and only this position, buildable
--      without co-position content — and not one of the coarse driver facts
--      travelling beside it.  (The error also exhibits the two components the
--      §11 finding turns on: a producer phase and a relay phase.)
--
-- (M3  the DISPATCH, `parked-at`)  route the `lpUpSrv` clause to `oUpCell`.
--      *** RED as predicted ***: `:1431.74-76: error: [UnequalTerms] BFsPos !=
--      (SysMedium.CopyPhase blkA) of type Set when checking that the expression
--      at has type AtPos l lpUpCell b (toSys r)`, EXIT=42.  So the six
--      same-SHAPED residual fields cannot be cross-wired: each position's own
--      occupied-component TYPE catches a mis-route, which is the guard that
--      matters most in a dispatch whose arms are six copies of one interface.
--
-- (M4  the HIDE side condition, `noUpClient-BD`)  `hidden-upRecv-AB` →
--      `hidden-upRecv-AC`.  *** GREEN — a NON-mutation, and the FINDING is the
--      MIRROR of instalment 2's M2. ***  `keptB blkA (_ , apiBF linkAB hi
--      recvBFBlock) x` and its `linkAC` twin are DEFINITIONALLY EQUAL: the
--      receive clause's link test is `⌊ l ≟ linkBD ⌋ ∨ ⌊ l ≟ linkCD ⌋`, which is
--      `false` on BOTH up links, so the conjunction short-circuits before the
--      block is ever consulted.  Consequences worth keeping: (a) on the HIDDEN
--      side the load-bearing content is the CHANNEL AND ROLE (a `recvBFBlock` on a
--      non-D link), never the link and never the block — which is why
--      `hidden-upRecv-*` needs no `blkA-refl` and holds at the EXISTENTIAL block,
--      i.e. §9's block-freeing is what lets §10 quantify over `b`; (b) instalment
--      2 measured the same collapse on the KEPT side (both DOWN links
--      definitionally equal), so the pair of findings says the hide condition is
--      block-sensitive on the kept side and role-sensitive on the hidden side,
--      and NO link-swap mutation can ever test either.
--
-- (M5  the HIDE side condition, EFFECTIVELY — the mutation M4's own analysis
--      identified as the load-bearing one, run in the fix round at the reviewer's
--      request since M4 turned out to be a definitional no-op.)  In
--      `hidden-upRecv-AB` (`:1340-1341`) swap the ROLE: `recvBFBlock` →
--      `sendBFBlock` (plus the one import that constructor needs, which is the
--      whole of the rest of the mutation).
--      *** RED as predicted ***: `:1341.22-26: error: [UnequalTerms]
--      Relation.Nullary.isYes (FourNodeDiamond.go x blkA) != false of type Bool
--      when checking that the expression refl has type mem (hidden blkA) (Block₃ ,
--      apiBF linkAB hi sendBFBlock) x`, EXIT=42.  *** THE ERROR IS THE POINT ***:
--      with the role swapped the condition no longer short-circuits — it reduces to
--      the BLOCK test `⌊ x ≟ blkA ⌋`, because A's produce on `linkAB` at `hi` IS a
--      KEPT event (`keptB`'s send clause admits `linkAB ∨ linkAC`).  So the hide
--      side condition of §10 is genuinely ROLE-sensitive and the up-link receive's
--      hidden-ness is NOT vacuous; M4's link swap could not see this because the
--      receive clause's link test fails identically on both up links.
------------------------------------------------------------------------

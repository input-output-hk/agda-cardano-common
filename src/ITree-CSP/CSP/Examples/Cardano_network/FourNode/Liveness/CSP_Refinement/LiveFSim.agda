{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `LiveFSim` — THE FAILURE-SIMULATION WITNESS of the four-node CSP-refinement
-- liveness target, i.e. the assembly of everything the six preceding campaigns
-- built into `Semantics.BisimFromRel.FSimFromRel` and out through
-- `Semantics.FailureSim.fsim→⊑FD`:
--
--     lspec-fd : LSpec blkA true true ⊑FD (abstractSystem ∖ hidden blkA)
--
-- INSTALMENT 1: the RELATION, its seed at the initial pair, the two obligations
-- that are already theorems (`stabR`, `ndivL`), the `√` arm, and the CONCLUSION
-- at the two remaining obligations stated as `FwdT`/`FwdE` — wired, not
-- documented, so the next instalment's only job is to inhabit those two types
-- and delete the `Assemble` header.
--
-- INSTALMENT 2: `noRetA` narrowed to the invariant the `Rel` already carries
-- (§4's last bullet), and *** `fwdT : FwdT` DISCHARGED *** — the FLAG LAYER (§A,
-- premise-free: "a hidden step moves no reader of the coupling", including the
-- produce-threshold refutation the driver layer cannot see) plus the class
-- dispatch (§B).  `Assemble` now takes `fwdE` alone.
--
-- INSTALMENT 3 (the CLOSE): *** `fwdE : FwdE` DISCHARGED *** — the KEPT-side
-- flag layer (§C: the `keptB` row inversions, the two label decoders that give
-- the co-leg gate a NON-HIDDEN argument, the per-leg reader fixities, the
-- `keptRecv⇒prod` residue off `LegInv`, the spec move per class) plus the three
-- classes and the 20-clause dispatch (§D).  `Assemble` now takes NOTHING, so
-- `lspec-fd` holds at this module's parameters and nothing else.  The `√` class
-- is wired, which is what finally makes (P5) `noRetA` EXERCISED rather than
-- dead.  THE COST OF THE CLOSE was (P6)-(P8): three successor-side component
-- equations that the two frozen inversions build and then project away.  (P6) is
-- NOW A THEOREM (§A4, on the widened `break-invert`), so is (P7) (§A5, on the ⁺
-- cone's own kept `SrvLands`) and so is (P8) (§A6, on owner grant #5: the node-D
-- peel carries the consume-driver step it already had).  *** ALL THREE ARE
-- DISCHARGED *** — see the premise block's own note, and §15 of the report.
--
-- ---------------------------------------------------------------------
-- RE-DERIVATION OF THE PLAN'S TASK-5 BRIEF (it predates all six campaigns).
-- Verdict per claim, re-derived against the sources at the time of writing:
--
--   1. `FSimFromRel`'s four parameters and their order — CURRENT
--      (`Semantics/BisimFromRel.agda:96-108`: `Rel`, `fwdE`, `fwdT`, `stabR`,
--      `ndivL`; `rel→fsim` at `:112`; "`p` is the IMPLEMENTATION, `q` the
--      SPECIFICATION" at `:86`).
--   2. `fsim→⊑FD : FSim R Q P → P ⊑FD Q` — CURRENT (`Semantics/FailureSim.agda:196`,
--      not `:196`-as-a-module-line: the declaration itself).  The two conventions
--      do agree; nothing to "fix".
--   3. "`LegInv` for BOTH legs rides inside the relation" — SUPERSEDED.  The
--      object to carry is the assembly's `LegJointB` (`LiveLegAssembly:656`),
--      which is `(l : TwoLegs) → LegJoint⁺ l s` — i.e. `PipeInvS × LegInv ×
--      TokenExcl × PipeVal` at BOTH legs.  Two `LegInv` factors would be too
--      weak (no block pin — the F2/G5 finding) and structurally wrong (the four
--      components' arms consume each other's facts).
--   4. "`RState` carries `reach`, so reachability is free / no `Reachable`
--      induction" — CURRENT and load-bearing (`SysReach.agda:143-147`; the
--      `rStepʷ` padding at `:137-138` is why induction is the wrong route).
--   5. "`fwdE`/`fwdT` are `legJoint-step`" — WRONG, twice over.  (a) The fold is
--      the WEAK-move packaging; the FSim wants the two STRONG classes, which are
--      the assembly's `tauStepB`/`evStepB` (this is booked gap G1, and the
--      correction is sharper than G1 stated it: the fits are the ⁺⁺-level
--      `tauStepB`/`evStepB`, NOT the `LegJoint`-level `tauStepJ`/`evStepJ` the
--      charter named, because the `Rel` carries `LegJointB`).  (b) Those
--      theorems are the INVARIANT half only: they deliver `r′` and
--      `M ≡ radec r′`, never the spec move (gap G2).  INSTALMENT 2 sharpened
--      this once more: the consumable objects are the CLASS ARMS one level
--      below those two dispatchers (`τpreserveB-med`/`tauIoB-in`/`tauIoB-out`/
--      `evStepB-api`), because a `with`-defined dispatcher's successor does not
--      reduce for a variable step — see §B's own note for the mechanics.
--   6. "`LiveNoDivH.Descent.noDivH` IS `ndivL` directly" — CURRENT, verified at
--      `LiveNoDivH.agda:376-377`, and it is taken here as a single abstract fact
--      rather than by threading `Descent`'s six parameters (see §3).
--   7. "`stabR` is `LiveStableOffer.stabOffer` + two `LegInv` factors" —
--      SUPERSEDED by something strictly better: `stabR-final`
--      (`LiveStableOffer.agda:1693-1694`) takes `LegJointB` + `InFlightOpen` at
--      the two legs and its `Settle` output matches `FSimFromRel.stabR`'s field
--      FIELD FOR FIELD (verified in §2, not assumed).
--   8. "`keptRecv⇒prod`" — SUPERSEDED (it turned out a projection off the
--      block-indexed `AtPos`); `fwdE` uses the `-may` spec transitions, which
--      need no flag-exact source at all.
--   9. The `√` arm ("refuted: the KA client is frozen, take the refutation as a
--      parameter discharged in Task 6") — HALF WRONG, and this is the
--      instalment's one structural finding: see §4.  The refutation is NOT
--      available from `WalkBrkFire.unb-ret-⊥` (that needs an UNBROKEN link,
--      which no reachable-state fact supplies once every link may break), and
--      the arm cannot be "handled" instead, because no spec state can `√`.
--  10. "Phase 1 supplies no hidden-class preservation lemmas; Task 5 must build
--      them (≈150-300)" — CURRENT, and the hidden-receive hazard it records (a
--      hidden receive of `b′ ≢ blkA` really does cross `cp3 → cp4`, and only
--      `recvOf`'s payload conjunct keeps `delivD` fixed) is re-derived as REAL:
--      `recvOf (consD b ph) = if pastRecv ph then ⌊ b ≟ blkA ⌋ else false`
--      (`LiveSpecCouple.agda:181-182`).
--  11. The `fwdE` class table (5 kept classes, the flag lemma and the spec
--      transitions per class) — CURRENT as a table; its anchors have shifted and
--      are re-derived in §6's price note.  `keptB` really is a closed 4-class
--      alphabet (`Spec.lagda.md:110-115`).
--  12. "`Rel` needs `LegInv legBD × LegInv legCD`" (assembly gap G4) — SOLVED
--      BY THE OBJECT: `LegJointB`'s ∀ is over the two legs, and its own leg
--      INDEX is vestigial (`LiveLegAssembly:658-666`), so ONE conjunct at
--      `legBD` carries both legs.
--
-- ---------------------------------------------------------------------
-- THE PREMISE AUDIT OF `lspec-fd` — the campaign's headline, stated exactly.
-- `lspec-fd` (§7) holds at, and only at, these premises:
--
--   (P1) `cellCp3` — *** RETIRED AT THE CELLCP3 WINDOW; A RETIRED NAME FROM HERE ON.
--        `lspec-fd` HOLDS AT NO PREMISE OF THIS KIND AT ALL. ***  It read
--        `(l : TwoLegs) (b : Block₃) (r : RState) → LS.CellCp3 l b r` (the cell/reader
--        alignment; owner decision #4) with the parked supplier interface
--        `LiveTokenExcl.cellCp3-of`.  That route was not the one taken: it is a
--        THEOREM off the CARRIED join, `LiveChanJoin.cellCp3-of` (§5e), consumed
--        inside `LiveChanJoin`'s own io READ arm, so it never reaches `Sim`'s
--        telescope and `LivenessProof.Premises` is EMPTY.
--   (P2)/(P3) `InFlightOpen legBD` / `legCD`, at every reachable `r` AND AT THE
--        CARRIED INVARIANT (`:1275-1276` — re-derived at the post-close fix round; the old
--        `:1231-1232` had drifted 44 lines — the parameters take
--        `LCJ.LegJointUB legBD (toSys r)`, because eight of the twelve facts are
--        theorems whose premises include the PROVED `NoTwoTokens`).
--        *** NOT 12 ASSUMED POSITION FACTS ANY MORE (Task 4). ***  The supplier
--        `LivenessProof.At.ifo-of` (`LivenessProof:432`, re-derived at the window's
--        close — `:399-454` was T12's reading and `:297-314` the one before it) BUILDS
--        both records:
--        the four cell positions off `LiveChanInv.cellOpen-up-chan`/`-dn-chan`,
--        the four server positions off `LiveSrvOpen.srvOpen-up`/`-dn` (both
--        families at the hop's own `ChanUp`/`ChanDn` + the carried exclusions +
--        the link antecedent the fields now carry), and the four relay-driver
--        positions off `LiveRelayCS.relayOpen-in-s′`/`-out-s′`, i.e. modulo an api
--        residual of *** ZERO *** equations (T11h).  *** (T8c-iii) THIS IS THE THIRD
--        COUNT SITE AND IT WAS THE STALEST: *** it read SEVEN (correct only until T5)
--        and named `csRes`, a field that no longer exists.  Nine before the cross-node
--        api campaign; `pp4` went at T1, `pp5` at T2, `pp1` at T5, `pp2` at T6d and
--        `cp5` at T7 — those five off the carried `LiveDrvBF.DrvBF` — `cp6`/`pp0` at
--        T8c-iii off the carried `LiveDrvCSD.DnJoint` instead, `cp4` at T10 off the
--        carried `LiveDrvBFA.UpJoint`, and `pp3` — the last of all nine — at T11h off
--        the carried `LiveDrvBFD.BFFresh` through `LiveRelayCS` §3's `Sharp`; the
--        latter three are the discharges whose equations could not move into `DrvCp`.
--        *** So `LiveRelayCS.CSAt` and `.BFAt` are `⊤` at all seventeen shapes
--        (`csResidual-triv`, `bfResidual-triv`) and what `LivenessProof` assumes
--        instead is its ONE `Premises` field: `cellCp3` ALONE (`csRes` RETIRED at
--        T8c-iii, `bfRes` at T12). ***  (SUPERSEDED IN PLACE AT THE CELLCP3 WINDOW:
--        `cellCp3` went the same way, so `LivenessProof` assumes NOTHING and
--        `Premises` has ZERO fields.)  Neither hop's channel invariant is
--        assumed at all any more: `LiveChanJoin` carries the WHOLE `ChanLeg` in this
--        module's own `Rel`, and since T8c-iii node D's `DnJoint` beside it.
--        (SUPERSEDED IN PLACE: this read "the `isStable`-scoped **TWO**-equation api
--        residual — `cp4` and `pp3`, both BlockFetch and both cross-node" and "its
--        **TWO** `Premises` fields — `cellCp3` and `bfRes` (T10: `bfRes` is now ONE
--        equation, `pp3` …)" until T12.)
--        *** THE BANKED RULE IS THREE FILES, NOT TWO — AND T11h PROVED IT BY MISSING
--        THIS ONE. ***  The T6d rule said "sweep BOTH count files or neither"
--        (`LivenessProof`'s header and `STABR_STATUS.md`); this site is a THIRD, and it
--        went five arms stale because it carries a NUMBER inside a CLAIM rather than on
--        a count line.  T11h swept the two named files, recorded the sweep as
--        "COMBINED SWEEP of both count files", and left this site saying `bfRes` was
--        ONE equation when it was zero — so the rule's own restatement was the error.
--        *** THE RULE, FINAL (T12): the count lives in THREE files — this one,
--        `LivenessProof`'s header, and `STABR_STATUS.md` — plus TWO further sites in
--        THIS file that drift with it (§4's `Rel` note and §7's premise-family count).
--        After any retirement, grep the retired NAMES across `CSP_Refinement`, not just
--        the count lines. ***
--   (P4) `noDivH` — divergence-freedom of `radec r ∖ hidden blkA` at every
--        reachable `r`.  NOT an assumption of the effort: it is a THEOREM of
--        `LiveNoDivH.Descent` at that module's six banked-lemma parameters,
--        which `LiveHeavyFacts` supplies (and `LivenessProof` passes on by
--        name).  Taken abstractly here to keep this module's closure off the
--        heavy `LTL/Walk/*` suffix.
--   (P5) `noRetA` — DISCHARGED (§4): "no reachable abstract config WHOSE JOINT
--        INVARIANT HOLDS forces to `ret`" is now a THEOREM, because the joint
--        invariant CARRIES the inert-freeze conjunct.  `LegJointB`'s per-leg
--        product gained `LiveRetFree.KAcFrz` — node B's link-AB KA client sits at
--        its loop head, whose coarse image `NS.kcClient` is not `Fin` — and
--        `LiveRetFree.radec-noRet` peels a `ret` of the whole abstract decode
--        down to that one peer in eight banked `SysSqrt` rungs.  The conjunct is
--        preserved by every class: the medium-τ and `break` successors keep all
--        four node records literally, and the api and io classes report the fired
--        bundle's freeze answer (owner grant #6's third fact family in
--        `PipeNodeIoEvo`, and `driverExpose⁺`'s `deFrzB` field).
--   (P6) `brkBits` — DISCHARGED (§A4): `PES.break-invert` was widened to carry
--        the `broken`-bit update it always built, and the premise left this
--        telescope.  (P7) `prodLands` — DISCHARGED TOO (§A5): the ⁺ cone now
--        KEEPS the generic `SrvLands` its own `srvUp-of` built, and exports the
--        fired-link pin its node-A peels already took.  (P8) `recvLands` —
--        DISCHARGED AS WELL (§A6), on owner grant #5: `NodeDDrv` carries the
--        FIRING CONSUME-DRIVER STEP, off which the cone recovers both the `cp3`
--        gate the SESSION-40 anchor needs and the fired link that refutes the
--        co-leg.  So INSTALMENT 3's three KEPT-CLASS SUCCESSOR FACTS are all
--        theorems and none of them is a premise anywhere any more.
--        Each is a component equation at the invariant arm's OWN successor which
--        the frozen inversion BUILDS and then projects away (`break-invert`
--        keeps the cell phases but drops the `broken` update; `driverExpose⁺`
--        decides which driver fired and then reports a four-arm disjunction whose
--        `ldFix` arm fits every label).  TRUE by those very peels, step-local,
--        NOT recoverable downstream (the peels do not reduce for a variable step
--        and no decode is injective), and discharged by WIDENING the two
--        inversions: `break-invert` +1 field (TAKEN, ≤ 25 lines plus the
--        pointwise restatement the funext gap forces), the cone ≈ 200-400.  The
--        premise block below states each at the exact term the arm's successor
--        δ-reduces to, and argues the negative claim in full.
--
-- `FwdT` (instalment 2, §B) and `FwdE` (instalment 3, §D) are DISCHARGED — they
-- are obligations of the FSim, not premises of the effort, and neither is a
-- parameter of anything any more.
--
-- Nothing else.  In particular NO block premise, NO window premise, NO parked
-- premise, and no `Reachable` induction anywhere.
--
-- ---------------------------------------------------------------------
-- CONTENTS (the section letters are historical, one per instalment; this is the
-- reading order).
--
--   §1   the FSim RELATION, its seed, the `specPos` regression         (instalment 1)
--   §A   the HIDDEN-side flag layer + the produce-threshold refutation (instalment 2)
--   §C   the KEPT-side flag layer: row inversions (§C1), the two label
--        decoders and the co-leg gate (§C2), the per-leg reader fixities
--        (§C3), `keptRecv⇒prod` off `LegInv` (§C4), the spec move per
--        class (§C5)                                                  (instalment 3)
--   `Sim`  the premise block — *** THREE parameters ***: (P2)-(P4) of the audit
--          above, in order, and NONE of them is a premise (`ifoBD`/`ifoCD` are
--          applications of the carried join, `noDivH` is a theorem).  (SUPERSEDED IN
--          PLACE: this read "FOUR parameters: (P1)-(P4)"; (P1) `cellCp3` left the
--          telescope at the cellCp3 window.)  (P1) and (P5)-(P8) are NOT among them —
--          `LiveChanJoin` §5e discharges (P1) and §4/§A4/§A5/§A6 prove the rest.
--   §2   `stabR`   · §3 `ndivL`   · §4 the `√` arm and `sqrt-⊥`
--   §5/§6 the two obligation TYPES `FwdT`/`FwdE`
--   §B   `fwdT` — the τ obligation, discharged                        (instalment 2)
--   §D   `fwdE` — the visible obligation, discharged, with the two
--        successor-identity `refl` probes at its head                 (instalment 3)
--   §7   `Sim.Assemble.lspec-fd` — THE CONCLUSION
--
-- ---------------------------------------------------------------------
-- DISCIPLINE.  No postulates, holes, `--allow-unsolved-metas`,
-- `NON_TERMINATING` or `mutual`.  Every imported module is READ-ONLY.  One
-- `import M blkA` per parameterised module.  The premises live in NAMED inner
-- modules (`Sim`, `Sim.Assemble`) because their types mention `RState`/`hidden`,
-- which exist only after the `blkA` header — the house pattern of
-- `LiveNoDivH.Descent`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveFSim
  (blkA : Block₃) where

open import Level using ( 0ℓ )
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Bool using ( Bool; true; false; _∨_; _∧_ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Relation.Nullary using ( Dec; yes; no )
open import Relation.Nullary.Decidable using ( ⌊_⌋ )
open import Class.DecEq using ( _≟_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI; isStable; ret )
open PTree using ( force )

------------------------------------------------------------------------
-- The shared alphabet, the operator layer, and the semantic vocabulary the
-- four obligations are stated in.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD; DecEq-Block₃ )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; break; sendBFBlock; recvBFBlock
  ; sendBFRequestRange; sendBFClientDone; sendBFStartBatch; sendBFNoBlocks
  ; sendBFBatchDone; reqBFRange
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; done; input; output
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi; lo; IDs; DecEq-Dir )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∖_; _∥⇘_⇙_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; evLabel; Event√; evl; √; ev; τ; _─[_]─►_; Diverges )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; _═[_]═►_; wτ; τ*-refl )
open import Semantics.Refusals {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Offers )
open import Semantics.FailuresDivergences
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using ( _⊑FD_ )
open import Semantics.FailureSim
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using ( FSim; fsim→⊑FD )
open import Semantics.BisimFromRel
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using ( module FSimFromRel )

-- the OUTER hide's single-step inversions: `Hide-ev-elim` is what makes the `√`
-- arm decidable at all (`he√` pins a `√` of `P ∖ A` to `force P ≡ ret`)
import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload}) as TLH

------------------------------------------------------------------------
-- The reachable-config carrier and the campaign's objects.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys; rinit; radec-init )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( broken; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; ConsDPh; consD; cblk; cph; NodeStateD
        ; BFsPos; bsBlk1; prod-AB; prod-AC; cons-BD; cons-CD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( absNodesOf
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( IsApiCSBF; aicCS; aicBF; aicDone )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( oevB-no-io; oevB-refute )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD; phOf; cblkOf; linkOf; InCp03 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ProdAdv; ConsAdv; c01; c12; c23; c34; c45; c56 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor blkA
  using ( ConsHeld )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; ProdSent; ProdNotSent; prodSent-notSent-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriver blkA
  using ( ProdStepKind; pMove; pSend; prodadv-step )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriverCone blkA
  using ( LegDriverStep; ldProd; ldRelay; ldCons; ldFix
        ; LegValStep; lvUpSrv; lvCons; SrvValEvo; upLinkOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( SrvCoupled; upSrv )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvStep blkA as PES
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA as LI
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone blkA
  using ( top-nodes-io-evoP⁺ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiExpose blkA
  using ( driverExpose⁺; VisLeaves⁺; vProdSend
        -- (P7)/(P8) §A5/§A6: the cone's own landing slots, per leg
        ; driverExpose⁺-prodLands; driverExpose⁺-recvLands
        -- (T3b) the cone's report is a RECORD; these are the slots this module reads
        ; deSucc; deMed; deLdBD; deLdCD; deVlBD; deVlCD; deLvBD; deLvCD )
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegStep blkA as LS
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegAssembly blkA as LA
-- (the ChanLeg join) the assembly's invariant WITH the leg's UP-hop channel
-- invariant, and the five arms that carry it — the object the `Rel` now holds
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanJoin blkA as LCJ
-- (P5) §4's discharge: the `ret` refutation at the inert-freeze conjunct, which
-- `LegJointB` now CARRIES (`LiveLegAssembly:657`'s trailing component)
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveRetFree blkA as LRF
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer blkA
  using ( InFlightOpen; stabR-final )

------------------------------------------------------------------------
-- The specification and the coupling.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( SpecProc; LSpec; Prod; Done; hidden; keptB )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveSpecCouple blkA
  using ( SpecOf; SpecOf-idle; specPos; specPosS; procOf
        ; SpecPos; posIdle; posProd; posDone; mkPos
        ; mkPos-cong; mkPos-done; prod1A; prod2A; delivD; g1F; g2F; recvOf
        ; pastSend; pastRecv; blkA-refl; recvOf-hit
        ; brkSet; brkPos; setP1; setP2
        ; specPos-break′; specPos-produce₁; specPos-produce₂
        ; specPos-recv₁; specPos-recv₂
        ; evBrk; evPrd; evRcv
        ; spec-ev-break; spec-ev-break-prod; spec-ev-break-done
        ; spec-ev-produce₁; spec-ev-produce₂
        ; spec-ev-produce₁-prod; spec-ev-produce₂-prod
        ; spec-ev-produce₁-done; spec-ev-produce₂-done
        ; spec-ev-recv₁-may; spec-ev-recv₂-may
        ; spec-ev-recv₁-done; spec-ev-recv₂-done )

------------------------------------------------------------------------
-- §1  *** THE FSIM RELATION. ***
--
-- Settled against `FSimFromRel`'s FIELD TYPES rather than against the brief:
-- every field quantifies over BARE TREES `{p q p′}` and returns a bare tree, so
-- the relation must be stated on trees and carry its state coordinate
-- existentially, together with the two decode equations that let each obligation
-- recover it.  Matching both equations to `refl` in an obligation instantiates
-- `p` and `q` to the decode terms, which is what makes every arm below a
-- one-liner instead of a `subst` chain.
--
-- WHY THESE THREE FACTORS AND NO OTHERS:
--   · `r : RState` carries its own `Reachable` witness (`SysReach:143-147`), so
--     reachability is free and the successors that `tauStepB`/`evStepB` deliver
--     ARE `RState`s — no `Reachable` induction, which the `rStepʷ` padding
--     (`SysReach:137-138`) would otherwise force.
--   · `LegJointB legBD (toSys r)` is the ONE carried invariant (assembly §9): it
--     is `(l : TwoLegs) → (PipeInvS × LegInv × TokenExcl) × PipeVal` at that
--     state, i.e. both legs (gap G4) and the block pin (gap F2/G5).  Its leg
--     INDEX is vestigial — `LegJointB legCD s` is the same type — so `legBD`
--     here is a convention, not a per-leg reading (the trap named at
--     `LiveLegAssembly:658-666`).
--   · NOTHING about the spec beyond `q ≡ SpecOf r`: the coupling is a FUNCTION
--     of the config (`LiveSpecCouple:220-221`), so the spec coordinate is
--     determined, never guessed.
------------------------------------------------------------------------

-- the FSim relation: an implementation tree is the hidden abstract decode of a
-- reachable config whose joint invariant holds, and the spec tree is that
-- config's coupled spec state
Rel : NetProc → SpecProc → Set₁
Rel P Q = Σ[ r ∈ RState ]
            (P ≡ radec r ∖ hidden blkA)
          × (Q ≡ SpecOf r)
          × LCJ.LegJointUB legBD (toSys r)

-- THE SEED.  `radec-init : radec rinit ≡ abstractSystem` (`SysReach:183-184`)
-- gives the impl coordinate; `SpecOf-idle` (`LiveSpecCouple:225-227`) fed the
-- `refl` that `LiveSpecCouple:835`'s permanent regression test certifies
-- (`specPosS initial ≡ posIdle true true`, and `toSys rinit ≡ initial` is
-- `SysReach:175-176`, also `refl`) gives the spec coordinate; the invariant is
-- `legJointB-init`, which lived OUTSIDE the assembly's `cellCp3` parameter (retired
-- at the cellCp3 window — the assembly has no premise parameter any more), so
-- the seed is premise-FREE.
rel-init : Rel (abstractSystem ∖ hidden blkA) (LSpec blkA true true)
rel-init = rinit
         , cong (λ z → z ∖ hidden blkA) (sym radec-init)
         , sym (SpecOf-idle rinit refl)
         , LCJ.legJointUB-init legBD

-- the initial coupling really is the statement's left-hand side (a `refl`
-- regression test: it fails if `mkPos`, `posOf` or `procOf` ever move)
_ : specPos rinit ≡ posIdle true true
_ = refl

------------------------------------------------------------------------
-- §A  *** THE FLAG LAYER *** — "a HIDDEN step moves no reader of the coupling".
-- PREMISE-FREE (nothing here needs `cellCp3` — which since the window nothing does),
-- so it is stated outside `Sim`.
--
-- `specPos` reads exactly FOUR things off a config (`LiveSpecCouple:202-211`):
-- the medium's `broken` bits, node A's two produce phases through `pastSend`,
-- and node D's two consume slots through `recvOf`.  `FwdT` owes, for every
-- hidden class, that none of the four moved — and that is the whole content of
-- this section.  The two Boolean readers are thresholds:
--
--   · `pastSend` flips exactly at `pp5 → pp6`, the `a56` producer adjacency
--     (`WalkMeasure:256`), which fires `apiBF (upLinkOf l) hi sendBFBlock ! blkA`
--     — a KEPT event (`Spec.lagda.md:110-115`), so it cannot be a hidden hop;
--   · `recvOf` flips at `cp3 → cp4`, the `c34` consumer adjacency, which fires
--     `apiBF (linkOf l) hi recvBFBlock ! b″` — kept ONLY when `b″ ≡ blkA`, so a
--     hidden receive DOES cross the phase threshold and is stopped by `recvOf`'s
--     PAYLOAD conjunct alone (`LiveSpecCouple:181-182`).  That asymmetry is why
--     the two arms below look nothing alike.
--
-- The producer arm is the campaign's flagged risk: `LegDriverStep`'s `ldProd`
-- carries a bare `ProdAdv` and NO label (`PipeEvDriverCone:621`), so `a56`
-- cannot be refuted from the driver layer.  It is refuted from the SERVER layer
-- instead — `VisLeaves⁺.vProdSend` + `LegValStep.lvUpSrv` + the `SrvCoupled`
-- half of the invariant the `Rel` already carries (see `prod-cross-⊥`).
------------------------------------------------------------------------

-- the coupling's four readers: if none of them moved, `specPos` did not move
specPos-of : (r : RState) (s′ : SysState)
           → broken (med s′) ≡ broken (med (toSys r))
           → prod1A (nA s′) ≡ prod1A (nA (toSys r))
           → prod2A (nA s′) ≡ prod2A (nA (toSys r))
           → delivD (nD s′) ≡ delivD (nD (toSys r))
           → specPosS s′ ≡ specPos r
specPos-of r s′ eb e1 e2 ed = mkPos-cong ed e1 (cong g1F eb) e2 (cong g2F eb)

-- the KEPT-ness of a fired label, as a TRANSPORTABLE predicate: the two
-- `evLabel`s of a fired-label equation carry different carrier `Set`s and `Set`
-- is not injective, so the tag must ride as a `Set`-valued predicate rather than
-- be matched by `refl` (`PipeProdFire:120-131`'s `IsSBB` rule)
KeptEv : Event → Set
KeptEv (evLabel X e a) = keptB blkA (X , e) a ≡ true

-- the HIDDEN-ness of a fired label, transportable for the same reason
HidEv : Event → Set
HidEv (evLabel X e a) = keptB blkA (X , e) a ≡ false

-- kept and hidden are exclusive.  Stated at the EVENT (not at `X`/`e`/`a`
-- implicits): the two predicates are stuck applications of `keptB`, so an
-- implicit event could never be solved at a `subst` call site.
kept-hid-⊥ : (w : Event) → KeptEv w → HidEv w → ⊥
kept-hid-⊥ (evLabel X e a) kt hd with trans (sym kt) hd
... | ()

-- A's produce of `blkA` on EITHER leg's upstream link is kept (`blkA-refl`
-- unblocks the payload test, which is the only non-computing conjunct)
kept-prod : (l : TwoLegs)
          → keptB blkA (Block₃ , apiBF (upLinkOf l) hi sendBFBlock) blkA ≡ true
kept-prod legBD = blkA-refl
kept-prod legCD = blkA-refl

-- a HIDDEN receive on a leg's own link has a payload that is NOT `blkA`, so the
-- slot it records reads `recvOf ≡ false` — the payload conjunct doing the work
recv-hid : (l : TwoLegs) (b″ : Block₃)
         → keptB blkA (Block₃ , apiBF (linkOf l) hi recvBFBlock) b″ ≡ false
         → recvOf (consD b″ cp4) ≡ false
recv-hid legBD b″ h = h
recv-hid legCD b″ h = h

-- the BF-server slot constructor is injective
bsBlk1-inj : {x y : Block₃} → bsBlk1 x ≡ bsBlk1 y → x ≡ y
bsBlk1-inj refl = refl

------------------------------------------------------------------------
-- §A1  THE PRODUCE READER.
------------------------------------------------------------------------

-- `pastSend` is the Boolean reading of `ProdSent` …
pastSend-sent : (ph : ProdPh) → ProdSent ph → pastSend ph ≡ true
pastSend-sent pp0 ()
pastSend-sent pp1 ()
pastSend-sent pp2 ()
pastSend-sent pp3 ()
pastSend-sent pp4 ()
pastSend-sent pp5 ()
pastSend-sent pp6 _ = refl
pastSend-sent pp7 _ = refl
pastSend-sent pp8 _ = refl
pastSend-sent pp9 _ = refl

-- … and its complement is the reading of `ProdNotSent`
pastSend-notSent : (ph : ProdPh) → ProdNotSent ph → pastSend ph ≡ false
pastSend-notSent pp0 _ = refl
pastSend-notSent pp1 _ = refl
pastSend-notSent pp2 _ = refl
pastSend-notSent pp3 _ = refl
pastSend-notSent pp4 _ = refl
pastSend-notSent pp5 _ = refl
pastSend-notSent pp6 ()
pastSend-notSent pp7 ()
pastSend-notSent pp8 ()
pastSend-notSent pp9 ()

-- every producer phase is on one side of the send threshold
prod-dich : (ph : ProdPh) → ProdSent ph ⊎ ProdNotSent ph
prod-dich pp0 = inj₂ tt
prod-dich pp1 = inj₂ tt
prod-dich pp2 = inj₂ tt
prod-dich pp3 = inj₂ tt
prod-dich pp4 = inj₂ tt
prod-dich pp5 = inj₂ tt
prod-dich pp6 = inj₁ tt
prod-dich pp7 = inj₁ tt
prod-dich pp8 = inj₁ tt
prod-dich pp9 = inj₁ tt

-- a producer step that stays on ONE side of the threshold leaves the flag fixed
pastSend-move : (a b : ProdPh) → (ProdNotSent a → ProdNotSent b)
              → (ProdSent a → ProdSent b) → pastSend b ≡ pastSend a
pastSend-move a b fN fS with prod-dich a
... | inj₁ sa = trans (pastSend-sent    b (fS sa)) (sym (pastSend-sent    a sa))
... | inj₂ na = trans (pastSend-notSent b (fN na)) (sym (pastSend-notSent a na))

-- *** THE RISK ARM. ***  A HIDDEN api step cannot cross the send threshold.
-- The driver layer cannot see this (`ldProd` carries a label-free `ProdAdv`), so
-- the refutation is taken on the SERVER layer: crossing hands the leg's upstream
-- BF server the block (`vProdSend`), and the server slot's own evolution
-- (`lvUpSrv`) then has only three arms — it was already holding it (refuted by
-- `SrvCoupled`, which forces the producer to have SENT, contradicting the
-- crossing's own source premise), it is not holding it (contradicts
-- `vProdSend`), or it GAINED it on this very step, whose label the witness pins
-- to the kept produce (contradicting hiddenness).
prod-cross-⊥ : (l : TwoLegs) (s s′ : SysState)
               {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
             → keptB blkA (X , e) a ≡ false
             → SrvCoupled l s → VisLeaves⁺ l s s′
             → SrvValEvo (upLinkOf l) (upSrv l s) (upSrv l s′) e a
             → ProdNotSent (prodOf l s) → ProdSent (prodOf l s′) → ⊥
prod-cross-⊥ l s s′ hid sc vl (inj₁ fix) nN sS =
  prodSent-notSent-⊥ (prodOf l s)
    (proj₁ sc (subst BFsHasBlk (sym (trans fix (vProdSend vl nN sS))) tt)) nN
prod-cross-⊥ l s s′ hid sc vl (inj₂ (inj₁ nb)) nN sS =
  nb (subst BFsHasBlk (sym (vProdSend vl nN sS)) tt)
prod-cross-⊥ l s s′ {X} {e} {a} hid sc vl (inj₂ (inj₂ (b″ , lbl , eqb))) nN sS =
  kept-hid-⊥ (evLabel X e a)
    (subst KeptEv (sym lbl)
      (subst (λ z → keptB blkA (Block₃ , apiBF (upLinkOf l) hi sendBFBlock) z ≡ true)
             (sym (bsBlk1-inj (trans (sym eqb) (vProdSend vl nN sS))))
             (kept-prod l)))
    hid

-- ONE leg's produce reader across a hidden api step whose driver arm is `ldProd`
prod-flag : (l : TwoLegs) (s s′ : SysState)
            {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
          → keptB blkA (X , e) a ≡ false
          → SrvCoupled l s → VisLeaves⁺ l s s′
          → SrvValEvo (upLinkOf l) (upSrv l s) (upSrv l s′) e a
          → ProdAdv (prodOf l s) (prodOf l s′)
          → pastSend (prodOf l s′) ≡ pastSend (prodOf l s)
prod-flag l s s′ hid sc vl lv padv with prodadv-step padv
... | pMove fN fS = pastSend-move (prodOf l s) (prodOf l s′) fN fS
... | pSend nN sS = ⊥-elim (prod-cross-⊥ l s s′ hid sc vl lv nN sS)

------------------------------------------------------------------------
-- §A2  THE RECEIVE READER.
------------------------------------------------------------------------

-- every consumer phase is on one side of the receive threshold
cons-dich : (ph : ConsPh) → (ConsHeld ph × pastRecv ph ≡ true) ⊎ (pastRecv ph ≡ false)
cons-dich cp0 = inj₂ refl
cons-dich cp1 = inj₂ refl
cons-dich cp2 = inj₂ refl
cons-dich cp3 = inj₂ refl
cons-dich cp4 = inj₁ (tt , refl)
cons-dich cp5 = inj₁ (tt , refl)
cons-dich cp6 = inj₁ (tt , refl)

-- before the receive the slot reads `false` whatever block it carries (cased on
-- the PHASE, so each clause computes; the three past-receive rows are absurd)
recvOf-pre : (b : Block₃) (ph : ConsPh) → pastRecv ph ≡ false
           → recvOf (consD b ph) ≡ false
recvOf-pre b cp0 e = refl
recvOf-pre b cp1 e = refl
recvOf-pre b cp2 e = refl
recvOf-pre b cp3 e = refl
recvOf-pre b cp4 ()
recvOf-pre b cp5 ()
recvOf-pre b cp6 ()

-- a leg whose consume phase did not move keeps its delivery bit: the recorded
-- block is only read past the receive, and there `lvCons` fixes it
recvOf-fix : (b b′ : Block₃) (ph ph′ : ConsPh)
           → ph ≡ ph′ → (ConsHeld ph → b′ ≡ b)
           → recvOf (consD b′ ph′) ≡ recvOf (consD b ph)
recvOf-fix b b′ ph .ph refl held with cons-dich ph
... | inj₁ (h , _) = cong (λ z → recvOf (consD z ph)) (held h)
... | inj₂ pf      = trans (recvOf-pre b′ ph pf) (sym (recvOf-pre b ph pf))

-- the delivery bit across ONE genuine consume advance.  The `cp3 → cp4` hop is
-- the only one that crosses, and it is exactly where the label anchor pays: the
-- recorded block IS the fired payload, and a hidden receive's payload is not
-- `blkA`, so the successor slot still reads `false`.
recvOf-adv : (l : TwoLegs) (b b′ : Block₃) (ph ph′ : ConsPh)
             {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
           → keptB blkA (X , e) a ≡ false
           → ConsAdv ph ph′
           → (ph ≡ cp3 → Σ[ b″ ∈ Block₃ ]
                 (evLabel X e a ≡ evLabel Block₃ (apiBF (linkOf l) hi recvBFBlock) b″)
               × (b′ ≡ b″))
           → (ConsHeld ph → b′ ≡ b)
           → recvOf (consD b′ ph′) ≡ recvOf (consD b ph)
recvOf-adv l b b′ .cp0 .cp1 hid c01 anc held = refl
recvOf-adv l b b′ .cp1 .cp2 hid c12 anc held = refl
recvOf-adv l b b′ .cp2 .cp3 hid c23 anc held = refl
recvOf-adv l b b′ .cp3 .cp4 hid c34 anc held =
  let (b″ , lbl , eqb) = anc refl
  in  trans (cong (λ z → recvOf (consD z cp4)) eqb)
            (recv-hid l b″ (subst HidEv lbl hid))
-- the last two: `cp4`/`cp5`/`cp6` all read through the SAME `pastRecv ≡ true`
-- branch, so the phase written here is immaterial up to conversion
recvOf-adv l b b′ .cp4 .cp5 hid c45 anc held = cong (λ z → recvOf (consD z cp4)) (held tt)
recvOf-adv l b b′ .cp5 .cp6 hid c56 anc held = cong (λ z → recvOf (consD z cp4)) (held tt)

------------------------------------------------------------------------
-- §A3  ONE HIDDEN api STEP, BOTH READERS, BOTH LEGS.
------------------------------------------------------------------------

-- ONE leg's two coupling readers across a hidden api step.  Three of the four
-- driver arms fix the leg's producer and consumer outright; `ldProd` goes
-- through §A1's threshold argument and `ldCons` through §A2's.
legFlags : (l : TwoLegs) (s s′ : SysState)
           {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
         → keptB blkA (X , e) a ≡ false
         → SrvCoupled l s
         → LegDriverStep l s s′ e a → VisLeaves⁺ l s s′ → LegValStep l s s′ e a
         → (pastSend (prodOf l s′) ≡ pastSend (prodOf l s))
         × (recvOf (consD (cblkOf l s′) (phOf l s′))
            ≡ recvOf (consD (cblkOf l s) (phOf l s)))
legFlags l s s′ hid sc (ldProd padv re ce cue cde ue de) vl lv =
    prod-flag l s s′ hid sc vl (lvUpSrv lv) padv
  , recvOf-fix (cblkOf l s) (cblkOf l s′) (phOf l s) (phOf l s′) ce (lvCons lv)
legFlags l s s′ hid sc (ldRelay rk pe ce cue cde de ucl wUp bfx) vl lv =
    cong pastSend (sym pe)
  , recvOf-fix (cblkOf l s) (cblkOf l s′) (phOf l s) (phOf l s′) ce (lvCons lv)
legFlags l s s′ hid sc (ldCons cadv anc pe re cue cde ue dcl wDn) vl lv =
    cong pastSend (sym pe)
  , recvOf-adv l (cblkOf l s) (cblkOf l s′) (phOf l s) (phOf l s′) hid cadv
      (λ eq → let (b″ , lbl , cbe , _) = anc eq in b″ , lbl , cbe)
      (lvCons lv)
legFlags l s s′ hid sc (ldFix pe re ce cue cde ue de) vl lv =
    cong pastSend (sym pe)
  , recvOf-fix (cblkOf l s) (cblkOf l s′) (phOf l s) (phOf l s′) ce (lvCons lv)

-- *** A HIDDEN api STEP MOVES NO READER OF THE COUPLING. ***  The medium is
-- fixed by the cone's own `med` equation (so both path flags are), and the four
-- node readers are the two legs' two readers — which is exactly why the `Rel`
-- has to carry BOTH legs (assembly gap G4).
apiSpecFix : (r : RState) (s′ : SysState)
             {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
           → keptB blkA (X , e) a ≡ false
           → med (toSys r) ≡ med s′
           → SrvCoupled legBD (toSys r) → SrvCoupled legCD (toSys r)
           → LegDriverStep legBD (toSys r) s′ e a
           → LegDriverStep legCD (toSys r) s′ e a
           → VisLeaves⁺ legBD (toSys r) s′ → VisLeaves⁺ legCD (toSys r) s′
           → LegValStep legBD (toSys r) s′ e a → LegValStep legCD (toSys r) s′ e a
           → specPosS s′ ≡ specPos r
apiSpecFix r s′ hid meq scB scC ldB ldC vlB vlC lvB lvC =
  let (p1 , d1) = legFlags legBD (toSys r) s′ hid scB ldB vlB lvB
      (p2 , d2) = legFlags legCD (toSys r) s′ hid scC ldC vlC lvC
  in  specPos-of r s′ (cong broken (sym meq)) p1 p2 (cong₂ _∨_ d1 d2)

------------------------------------------------------------------------
-- §C  *** THE KEPT-SIDE FLAG LAYER *** — "a KEPT step moves exactly the readers
-- its own class owns, and NO others".  PREMISE-FREE, so it sits outside `Sim`.
--
-- `FwdE`'s five kept label classes (`Spec.lagda.md:109-115`: the four `break`s,
-- A's produce of `blkA` on AB/AC at `hi`, D's receive of `blkA` on BD/CD at
-- `hi`) each owe TWO things: the coupled flag UPDATE (a banked `specPos-*`
-- lemma, whose premises are component-level state equations) and the SPEC's own
-- weak move (a banked `spec-ev-*`).  This section builds the bridges:
--
--   · §C1 the `keptB` row inversions — with the label's link/direction/payload
--     read OFF the kept-ness equation rather than by an 8-clause dispatch (the
--     `keptB` row IS a conjunction of decisions, so two `_∧_` projections and
--     one `_∨_` split do the whole job);
--   · §C2 the two label DECODERS `sbbLink`/`rcvLink`.  *** THIS IS THE
--     NON-REUSABLE PIECE the gate priced the band top for. ***  §A's co-leg
--     arguments are `hid`-GATED (`prod-cross-⊥` refutes a threshold crossing by
--     contradicting HIDDENNESS), and a kept event has no such gate: the kept
--     event happens on ONE leg and the OTHER leg's readers must be shown fixed
--     by a PARALLEL NON-HIDDEN argument.  It is the same three-arm server
--     refutation with the hiddenness contradiction replaced by a LINK one — the
--     `SrvValEvo` gained arm NAMES its own leg's up-link, so a `sendBFBlock` on
--     the other leg's link refutes it, and a non-`sendBFBlock` label refutes it
--     outright.  Both are one `cong` on a `Maybe Link` decoder;
--   · §C3 the per-leg reader-fixity lemmas (`prodFlag-at`/`recvFlag-at`), the
--     non-hidden analogues of §A3's `legFlags`, SPLIT per reader because a kept
--     class needs its firing leg's OTHER reader fixed but not its own;
--   · §C4 the `keptRecv⇒prod` residue, discharged from `LegInv`: past its
--     receive a leg's token can only sit at `lpDone`, and NINE of the ten
--     `AtPos` clauses (`LiveLegInv:427-445`) hand over `ProdSent` outright;
--   · §C5 the spec-side move per class, dispatched on `SpecPos` so the call
--     sites stay `with`-free (the `pack` pattern of §A).
------------------------------------------------------------------------

-- select a per-leg datum: the ⁺ cone reports BOTH legs from ONE peel, and every
-- kept class needs the firing leg's and the other leg's, so the pair is indexed
-- rather than destructured twice (a second peel would name a second successor)
pickLeg : ∀ {ℓ} {A : TwoLegs → Set ℓ} → A legBD → A legCD → (l : TwoLegs) → A l
pickLeg x y legBD = x
pickLeg x y legCD = y

-- the leg NOT carrying the kept event (`specPos` reads BOTH legs)
coLeg : TwoLegs → TwoLegs
coLeg legBD = legCD
coLeg legCD = legBD

-- the Spec's produce-flag update owned by a leg's up-link
setP : TwoLegs → SpecPos → SpecPos
setP legBD = setP1
setP legCD = setP2

------------------------------------------------------------------------
-- §C1  THE `keptB` ROW INVERSIONS.
------------------------------------------------------------------------

-- a Boolean that is not `false` is `true` (`Hide-ev-elim`'s `heV` carries the
-- NEGATED membership, and every row inversion below wants the positive form)
bool-not-false : (b : Bool) → (b ≡ false → ⊥) → b ≡ true
bool-not-false true  h = refl
bool-not-false false h = ⊥-elim (h refl)

-- `false ≡ true` is absurd (named so the non-kept rows stay one-liners)
false-true : false ≡ true → ⊥
false-true ()

-- the left `_∧_` projection of a `≡ true`
∧-true-l : (x y : Bool) → x ∧ y ≡ true → x ≡ true
∧-true-l true  y e = refl
∧-true-l false y ()

-- the right `_∧_` projection of a `≡ true`
∧-true-r : (x y : Bool) → x ∧ y ≡ true → y ≡ true
∧-true-r true  y e = e
∧-true-r false y ()

-- one `_∨_` disjunct of a `≡ true` holds
∨-true : (x y : Bool) → x ∨ y ≡ true → (x ≡ true) ⊎ (y ≡ true)
∨-true true  y e = inj₁ refl
∨-true false y e = inj₂ e

-- a decision that answers `true` hands over its witness
dec-true : {A : Set} (d : Dec A) → ⌊ d ⌋ ≡ true → A
dec-true (yes q) e = q
dec-true (no ¬q) ()

-- *** EVERY `_∧_`/`_∨_` PROJECTION BELOW PASSES ITS BOOLEANS EXPLICITLY. ***
-- `_∧_` matches on its first argument, so `_x ∧ _y ≡ true` against a `keptB` row
-- is a NON-DECOMPOSABLE constraint and the metas block (measured: the first
-- build failed with `_x_675 ∧ _x_673 ∧ ⌊ a ≟ blkA ⌋ = (…) ∧ (…) ∧ (…)`, blocked
-- on `_x_675`).  Spelling the row out turns each use into a CONVERSION check,
-- which reduces both sides and succeeds.

-- a KEPT produce is at direction `hi` (the middle conjunct)
kept-prd-dir : (l₀ : Link) (d₀ : Dir) (a : Block₃)
             → keptB blkA (Block₃ , apiBF l₀ d₀ sendBFBlock) a ≡ true → d₀ ≡ hi
kept-prd-dir l₀ d₀ a kt =
  dec-true (d₀ ≟ hi)
    (∧-true-l ⌊ d₀ ≟ hi ⌋ ⌊ a ≟ blkA ⌋
      (∧-true-r (⌊ l₀ ≟ linkAB ⌋ ∨ ⌊ l₀ ≟ linkAC ⌋)
                (⌊ d₀ ≟ hi ⌋ ∧ ⌊ a ≟ blkA ⌋) kt))

-- a KEPT produce is on AB or AC (the `_∨_` conjunct)
kept-prd-link : (l₀ : Link) (d₀ : Dir) (a : Block₃)
              → keptB blkA (Block₃ , apiBF l₀ d₀ sendBFBlock) a ≡ true
              → (l₀ ≡ linkAB) ⊎ (l₀ ≡ linkAC)
kept-prd-link l₀ d₀ a kt
  with ∨-true ⌊ l₀ ≟ linkAB ⌋ ⌊ l₀ ≟ linkAC ⌋
         (∧-true-l (⌊ l₀ ≟ linkAB ⌋ ∨ ⌊ l₀ ≟ linkAC ⌋)
                   (⌊ d₀ ≟ hi ⌋ ∧ ⌊ a ≟ blkA ⌋) kt)
... | inj₁ e = inj₁ (dec-true (l₀ ≟ linkAB) e)
... | inj₂ e = inj₂ (dec-true (l₀ ≟ linkAC) e)

-- a KEPT produce carries `blkA` (the payload decision)
kept-prd-blk : (l₀ : Link) (d₀ : Dir) (a : Block₃)
             → keptB blkA (Block₃ , apiBF l₀ d₀ sendBFBlock) a ≡ true → a ≡ blkA
kept-prd-blk l₀ d₀ a kt =
  dec-true (a ≟ blkA)
    (∧-true-r ⌊ d₀ ≟ hi ⌋ ⌊ a ≟ blkA ⌋
      (∧-true-r (⌊ l₀ ≟ linkAB ⌋ ∨ ⌊ l₀ ≟ linkAC ⌋)
                (⌊ d₀ ≟ hi ⌋ ∧ ⌊ a ≟ blkA ⌋) kt))

-- a KEPT receive is at direction `hi`
kept-rcv-dir : (l₀ : Link) (d₀ : Dir) (a : Block₃)
             → keptB blkA (Block₃ , apiBF l₀ d₀ recvBFBlock) a ≡ true → d₀ ≡ hi
kept-rcv-dir l₀ d₀ a kt =
  dec-true (d₀ ≟ hi)
    (∧-true-l ⌊ d₀ ≟ hi ⌋ ⌊ a ≟ blkA ⌋
      (∧-true-r (⌊ l₀ ≟ linkBD ⌋ ∨ ⌊ l₀ ≟ linkCD ⌋)
                (⌊ d₀ ≟ hi ⌋ ∧ ⌊ a ≟ blkA ⌋) kt))

-- a KEPT receive is on BD or CD
kept-rcv-link : (l₀ : Link) (d₀ : Dir) (a : Block₃)
              → keptB blkA (Block₃ , apiBF l₀ d₀ recvBFBlock) a ≡ true
              → (l₀ ≡ linkBD) ⊎ (l₀ ≡ linkCD)
kept-rcv-link l₀ d₀ a kt
  with ∨-true ⌊ l₀ ≟ linkBD ⌋ ⌊ l₀ ≟ linkCD ⌋
         (∧-true-l (⌊ l₀ ≟ linkBD ⌋ ∨ ⌊ l₀ ≟ linkCD ⌋)
                   (⌊ d₀ ≟ hi ⌋ ∧ ⌊ a ≟ blkA ⌋) kt)
... | inj₁ e = inj₁ (dec-true (l₀ ≟ linkBD) e)
... | inj₂ e = inj₂ (dec-true (l₀ ≟ linkCD) e)

-- a KEPT receive carries `blkA`
kept-rcv-blk : (l₀ : Link) (d₀ : Dir) (a : Block₃)
             → keptB blkA (Block₃ , apiBF l₀ d₀ recvBFBlock) a ≡ true → a ≡ blkA
kept-rcv-blk l₀ d₀ a kt =
  dec-true (a ≟ blkA)
    (∧-true-r ⌊ d₀ ≟ hi ⌋ ⌊ a ≟ blkA ⌋
      (∧-true-r (⌊ l₀ ≟ linkBD ⌋ ∨ ⌊ l₀ ≟ linkCD ⌋)
                (⌊ d₀ ≟ hi ⌋ ∧ ⌊ a ≟ blkA ⌋) kt))

------------------------------------------------------------------------
-- §C2  THE TWO LABEL DECODERS — the non-hidden co-leg gate.
------------------------------------------------------------------------

-- the link a `sendBFBlock` observation carries.  `Set` is not injective, so a
-- fired-label equation cannot be matched on `refl`/`()`; a `Maybe Link` decoder
-- transports along it by ONE `cong` (`PipeProdFire:120-131`'s `IsSBB` rule, at
-- the link rather than at the tag — the tag alone cannot separate the two legs)
sbbLink : Event → Maybe Link
sbbLink (evLabel _ (apiBF l₀ _ sendBFBlock) _) = just l₀
sbbLink _                                      = nothing

-- "the fired observation is a `sendBFBlock` on link `l₀`", transportably
IsSbbAt : Link → Event → Set
IsSbbAt l₀ w = sbbLink w ≡ just l₀

-- the mirror decoder for D's receive
rcvLink : Event → Maybe Link
rcvLink (evLabel _ (apiBF l₀ _ recvBFBlock) _) = just l₀
rcvLink _                                      = nothing

-- "the fired observation is a `recvBFBlock` on link `l₀`", transportably
IsRcvAt : Link → Event → Set
IsRcvAt l₀ w = rcvLink w ≡ just l₀

-- a leg's up-link is NOT the other leg's, so a produce on one leg is never the
-- other leg's own produce (the co-leg gate at the produce class)
upLink-co-⊥ : (l : TwoLegs) → IsSbbAt (upLinkOf (coLeg l))
                                (evLabel Block₃ (apiBF (upLinkOf l) hi sendBFBlock) blkA) → ⊥
upLink-co-⊥ legBD ()
upLink-co-⊥ legCD ()

-- and a leg's own link is not the other leg's (the co-leg gate at the receive
-- class, needed only for the produce reader — the delivery reader is not read)
link-co-⊥ : (l : TwoLegs) (b : Block₃)
          → IsRcvAt (linkOf (coLeg l))
              (evLabel Block₃ (apiBF (linkOf l) hi recvBFBlock) b) → ⊥
link-co-⊥ legBD b ()
link-co-⊥ legCD b ()

------------------------------------------------------------------------
-- §C3  THE PER-LEG READER FIXITIES (the non-hidden analogues of §A3).
------------------------------------------------------------------------

-- *** THE PARALLEL NON-HIDDEN REFUTATION. ***  A step whose label is not THIS
-- leg's own produce cannot cross the leg's send threshold.  Arms one and two are
-- §A1's verbatim (they never used hiddenness); arm three — where §A1 contradicts
-- KEPT-ness — is contradicted by the LINK instead: the gained arm names the
-- label as a `sendBFBlock` on `upLinkOf l`, which the decoder reads off.
prod-cross-at-⊥ : (l : TwoLegs) (s s′ : SysState)
                  {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                → (IsSbbAt (upLinkOf l) (evLabel X e a) → ⊥)
                → SrvCoupled l s → VisLeaves⁺ l s s′
                → SrvValEvo (upLinkOf l) (upSrv l s) (upSrv l s′) e a
                → ProdNotSent (prodOf l s) → ProdSent (prodOf l s′) → ⊥
prod-cross-at-⊥ l s s′ ¬sbb sc vl (inj₁ fix) nN sS =
  prodSent-notSent-⊥ (prodOf l s)
    (proj₁ sc (subst BFsHasBlk (sym (trans fix (vProdSend vl nN sS))) tt)) nN
prod-cross-at-⊥ l s s′ ¬sbb sc vl (inj₂ (inj₁ nb)) nN sS =
  nb (subst BFsHasBlk (sym (vProdSend vl nN sS)) tt)
prod-cross-at-⊥ l s s′ ¬sbb sc vl (inj₂ (inj₂ (b″ , lbl , eqb))) nN sS =
  ¬sbb (cong sbbLink lbl)

-- ONE leg's PRODUCE reader across a step that is not that leg's own produce:
-- `ldProd` goes through the threshold argument, the other three arms fix the
-- producer outright
prodFlag-at : (l : TwoLegs) (s s′ : SysState)
              {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
            → (IsSbbAt (upLinkOf l) (evLabel X e a) → ⊥)
            → SrvCoupled l s
            → LegDriverStep l s s′ e a → VisLeaves⁺ l s s′ → LegValStep l s s′ e a
            → pastSend (prodOf l s′) ≡ pastSend (prodOf l s)
prodFlag-at l s s′ ¬sbb sc (ldProd padv re ce cue cde ue de) vl lv
  with prodadv-step padv
... | pMove fN fS = pastSend-move (prodOf l s) (prodOf l s′) fN fS
... | pSend nN sS = ⊥-elim (prod-cross-at-⊥ l s s′ ¬sbb sc vl (lvUpSrv lv) nN sS)
prodFlag-at l s s′ ¬sbb sc (ldRelay rk pe ce cue cde de ucl wUp bfx) vl lv =
  cong pastSend (sym pe)
prodFlag-at l s s′ ¬sbb sc (ldCons cadv anc pe re cue cde ue dcl wDn) vl lv =
  cong pastSend (sym pe)
prodFlag-at l s s′ ¬sbb sc (ldFix pe re ce cue cde ue de) vl lv =
  cong pastSend (sym pe)

-- the DELIVERY reader across ONE consume advance whose label is not this leg's
-- own receive.  The `cp3 → cp4` hop is the only crossing, and there the anchor's
-- label witness is contradicted by the decoder (§A2 contradicted HIDDENNESS
-- there instead — the one line that differs).
-- NOTE (as at §A2): the two last clauses' dot patterns are the one place a
-- `ConsPh` renumbering would fail silently-then-obscurely.
recvOf-adv-at : (l : TwoLegs) (b b′ : Block₃) (ph ph′ : ConsPh)
                {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
              → (IsRcvAt (linkOf l) (evLabel X e a) → ⊥)
              → ConsAdv ph ph′
              → (ph ≡ cp3 → Σ[ b″ ∈ Block₃ ]
                    (evLabel X e a ≡ evLabel Block₃ (apiBF (linkOf l) hi recvBFBlock) b″)
                  × (b′ ≡ b″))
              → (ConsHeld ph → b′ ≡ b)
              → recvOf (consD b′ ph′) ≡ recvOf (consD b ph)
recvOf-adv-at l b b′ .cp0 .cp1 ¬rcv c01 anc held = refl
recvOf-adv-at l b b′ .cp1 .cp2 ¬rcv c12 anc held = refl
recvOf-adv-at l b b′ .cp2 .cp3 ¬rcv c23 anc held = refl
recvOf-adv-at l b b′ .cp3 .cp4 ¬rcv c34 anc held =
  ⊥-elim (¬rcv (cong rcvLink (proj₁ (proj₂ (anc refl)))))
recvOf-adv-at l b b′ .cp4 .cp5 ¬rcv c45 anc held =
  cong (λ z → recvOf (consD z cp4)) (held tt)
recvOf-adv-at l b b′ .cp5 .cp6 ¬rcv c56 anc held =
  cong (λ z → recvOf (consD z cp4)) (held tt)

-- ONE leg's DELIVERY reader across a step that is not that leg's own receive:
-- three arms fix the consumer outright, `ldCons` goes through the hop argument
recvFlag-at : (l : TwoLegs) (s s′ : SysState)
              {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
            → (IsRcvAt (linkOf l) (evLabel X e a) → ⊥)
            → LegDriverStep l s s′ e a → LegValStep l s s′ e a
            → recvOf (consD (cblkOf l s′) (phOf l s′))
              ≡ recvOf (consD (cblkOf l s) (phOf l s))
recvFlag-at l s s′ ¬rcv (ldProd padv re ce cue cde ue de) lv =
  recvOf-fix (cblkOf l s) (cblkOf l s′) (phOf l s) (phOf l s′) ce (lvCons lv)
recvFlag-at l s s′ ¬rcv (ldRelay rk pe ce cue cde de ucl wUp bfx) lv =
  recvOf-fix (cblkOf l s) (cblkOf l s′) (phOf l s) (phOf l s′) ce (lvCons lv)
recvFlag-at l s s′ ¬rcv (ldCons cadv anc pe re cue cde ue dcl wDn) lv =
  recvOf-adv-at l (cblkOf l s) (cblkOf l s′) (phOf l s) (phOf l s′) ¬rcv cadv
    (λ eq → let (b″ , lbl , cbe , _) = anc eq in b″ , lbl , cbe)
    (lvCons lv)
recvFlag-at l s s′ ¬rcv (ldFix pe re ce cue cde ue de) lv =
  recvOf-fix (cblkOf l s) (cblkOf l s′) (phOf l s) (phOf l s′) ce (lvCons lv)

-- BOTH legs' delivery readers assemble into node D's flag (`ConsDPh` is a
-- RECORD, so a leg's slot IS its two accessors up to η)
delivD-fix : (s s′ : SysState)
           → recvOf (consD (cblkOf legBD s′) (phOf legBD s′))
             ≡ recvOf (consD (cblkOf legBD s) (phOf legBD s))
           → recvOf (consD (cblkOf legCD s′) (phOf legCD s′))
             ≡ recvOf (consD (cblkOf legCD s) (phOf legCD s))
           → delivD (nD s′) ≡ delivD (nD s)
delivD-fix s s′ d1 d2 = cong₂ _∨_ d1 d2

-- a leg's slot that is past its receive holding `blkA` reads DELIVERED
recvOf-set : (l : TwoLegs) (s : SysState)
           → pastRecv (phOf l s) ≡ true → cblkOf l s ≡ blkA
           → recvOf (consD (cblkOf l s) (phOf l s)) ≡ true
recvOf-set l s e1 e2 =
  trans (cong (λ z → recvOf (consD z (phOf l s))) e2) (recvOf-hit (phOf l s) e1)

------------------------------------------------------------------------
-- §C4  THE `keptRecv⇒prod` RESIDUE, off `LegInv`.
------------------------------------------------------------------------

-- a consumer past its receive is not in `cp0..cp3`
inCp03-recv-⊥ : (ph : ConsPh) → InCp03 ph → pastRecv ph ≡ true → ⊥
inCp03-recv-⊥ cp0 _  ()
inCp03-recv-⊥ cp1 _  ()
inCp03-recv-⊥ cp2 _  ()
inCp03-recv-⊥ cp3 _  ()
inCp03-recv-⊥ cp4 () _
inCp03-recv-⊥ cp5 () _
inCp03-recv-⊥ cp6 () _

-- past the receive the token's position forces `ProdSent`: NINE of the ten
-- `AtPos` clauses carry it outright, and `lpPreSend` — the one that carries
-- `ProdNotSent` — is refuted by its own `InCp03` conjunct
atPos-sent : (l : TwoLegs) (s : SysState) (b : Block₃) (k : LI.LegPos)
           → LI.AtPos l k b s → pastRecv (phOf l s) ≡ true → ProdSent (prodOf l s)
atPos-sent l s b LI.lpPreSend  (_ , _ , _ , inc) pr =
  ⊥-elim (inCp03-recv-⊥ (phOf l s) inc pr)
atPos-sent l s b LI.lpUpSrv    (_ , ps , _ , _) pr = ps
atPos-sent l s b LI.lpUpCell   (_ , ps , _ , _) pr = ps
atPos-sent l s b LI.lpUpClient (_ , ps , _ , _) pr = ps
atPos-sent l s b LI.lpRelayIn  (_ , ps , _)     pr = ps
atPos-sent l s b LI.lpRelayOut (_ , ps , _)     pr = ps
atPos-sent l s b LI.lpDnSrv    (_ , ps , _ , _) pr = ps
atPos-sent l s b LI.lpDnCell   (_ , ps , _ , _) pr = ps
atPos-sent l s b LI.lpDnClient (_ , ps , _ , _) pr = ps
atPos-sent l s b LI.lpDone     (_ , ps , _ , _) pr = ps

-- so a delivered leg's producer HAS sent (the Boolean form the coupling reads)
legInv-sent : (l : TwoLegs) (s : SysState) → LI.LegInv l s
            → pastRecv (phOf l s) ≡ true → pastSend (prodOf l s) ≡ true
legInv-sent l s (b , k , at) pr = pastSend-sent (prodOf l s) (atPos-sent l s b k at pr)

------------------------------------------------------------------------
-- §C5  THE SPEC-SIDE MOVE PER CLASS, dispatched on `SpecPos`.
------------------------------------------------------------------------

-- the spec answers a kept `break` from each of its three state classes, and its
-- target is exactly the coupling's own `brkPos` update
spec-break-move : (l₀ : Link) (P : SpecPos)
                → procOf P ═[ evBrk l₀ ]═► procOf (brkPos l₀ P)
spec-break-move l₀ (posIdle g1 g2)       = spec-ev-break l₀ g1 g2
spec-break-move l₀ (posProd p1 g1 p2 g2) = spec-ev-break-prod l₀ p1 g1 p2 g2
spec-break-move l₀ posDone               = spec-ev-break-done l₀

-- … a kept produce, with target the coupling's own `setP` update
spec-prod-move : (l : TwoLegs) (P : SpecPos)
               → procOf P ═[ evPrd (upLinkOf l) ]═► procOf (setP l P)
spec-prod-move legBD (posIdle g1 g2)       = spec-ev-produce₁ g1 g2
spec-prod-move legBD (posProd p1 g1 p2 g2) = spec-ev-produce₁-prod p1 g1 p2 g2
spec-prod-move legBD posDone               = spec-ev-produce₁-done
spec-prod-move legCD (posIdle g1 g2)       = spec-ev-produce₂ g1 g2
spec-prod-move legCD (posProd p1 g1 p2 g2) = spec-ev-produce₂-prod p1 g1 p2 g2
spec-prod-move legCD posDone               = spec-ev-produce₂-done

-- … and a kept receive, whose target is `Done`.  THE IDLE POSITION HAS NO
-- RECEIVE EDGE AT ALL (`idleτ`'s branches are Stop / four breaks / two
-- produces), which is why these two take the leg's PRODUCE FLAG: with it set
-- `mkPos` is `posDone` or `posProd … true …`, and both do offer the receive.
spec-recv-move-BD : (dl g1 p2 g2 : Bool)
                  → procOf (mkPos dl true g1 p2 g2) ═[ evRcv linkBD ]═► Done blkA
spec-recv-move-BD true  g1 p2 g2 = spec-ev-recv₁-done
spec-recv-move-BD false g1 p2 g2 = spec-ev-recv₁-may true g1 p2 g2

spec-recv-move-CD : (dl p1 g1 g2 : Bool)
                  → procOf (mkPos dl p1 g1 true g2) ═[ evRcv linkCD ]═► Done blkA
spec-recv-move-CD true  p1    g1 g2 = spec-ev-recv₂-done
spec-recv-move-CD false true  g1 g2 = spec-ev-recv₂-may true  g1 true g2
spec-recv-move-CD false false g1 g2 = spec-ev-recv₂-may false g1 true g2

-- the leg-indexed receive move at the coupled spec state: the flag is
-- substituted into the position's own `mkPos` application
spec-recv-move : (l : TwoLegs) (r : RState) → pastSend (prodOf l (toSys r)) ≡ true
               → SpecOf r ═[ evRcv (linkOf l) ]═► Done blkA
spec-recv-move legBD r e =
  subst (λ z → procOf (mkPos (delivD (nD (toSys r))) z (g1F (broken (med (toSys r))))
                             (prod2A (nA (toSys r))) (g2F (broken (med (toSys r)))))
               ═[ evRcv linkBD ]═► Done blkA)
        (sym e) (spec-recv-move-BD (delivD (nD (toSys r)))
                   (g1F (broken (med (toSys r)))) (prod2A (nA (toSys r)))
                   (g2F (broken (med (toSys r)))))
spec-recv-move legCD r e =
  subst (λ z → procOf (mkPos (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                             (g1F (broken (med (toSys r)))) z
                             (g2F (broken (med (toSys r)))))
               ═[ evRcv linkCD ]═► Done blkA)
        (sym e) (spec-recv-move-CD (delivD (nD (toSys r))) (prod1A (nA (toSys r)))
                   (g1F (broken (med (toSys r)))) (g2F (broken (med (toSys r)))))

-- the leg-indexed produce flag update (the two banked `specPos-produce` lemmas,
-- selected by the leg; `pastSend (prodOf legBD s)` IS `prod1A (nA s)`)
specPos-prod : (l : TwoLegs) (r r′ : RState)
             → broken (med (toSys r′)) ≡ broken (med (toSys r))
             → pastSend (prodOf l (toSys r′)) ≡ true
             → pastSend (prodOf (coLeg l) (toSys r′))
               ≡ pastSend (prodOf (coLeg l) (toSys r))
             → delivD (nD (toSys r′)) ≡ delivD (nD (toSys r))
             → specPos r′ ≡ setP l (specPos r)
specPos-prod legBD r r′ eb e1 e2 ed = specPos-produce₁ r r′ eb e1 e2 ed
specPos-prod legCD r r′ eb e1 e2 ed = specPos-produce₂ r r′ eb e2 e1 ed

-- the leg-indexed receive flag update (the two banked `specPos-recv` lemmas)
specPos-recvL : (l : TwoLegs) (r r′ : RState)
              → recvOf (consD (cblkOf l (toSys r′)) (phOf l (toSys r′))) ≡ true
              → specPos r′ ≡ posDone
specPos-recvL legBD r r′ e = specPos-recv₁ r r′ e
specPos-recvL legCD r r′ e = specPos-recv₂ r r′ e

-- the FwdT payload at one hidden step of the implementation: an
-- invariant-preserving reachable successor at which the coupled spec position is
-- the SOURCE's — i.e. the spec may STAY PUT, which is what makes the τ
-- obligation's weak move `wτ τ*-refl`
StepOut : (r : RState) (M : NetProc) → Set₁
StepOut r M = Σ[ r′ ∈ RState ]
                (M ≡ radec r′) × (specPos r′ ≡ specPos r)
              × LCJ.LegJointUB legBD (toSys r′)

-- assemble a `StepOut` into the FSim's τ obligation: the spec answers with the
-- EMPTY weak τ-move (`wτ τ*-refl`), which is legal for `τ̂` and is the only move
-- available — no spec state can reach `Prod`/`Done` by τ alone (every `idleτ`/
-- `prodτ` branch lands on a MENU, `Spec.lagda.md:260-300`), which is exactly why
-- §A has to prove the coupling FIXED rather than merely updated
pack : (r : RState) {M : NetProc} → StepOut r M
     → Σ[ Q′ ∈ SpecProc ] ((SpecOf r ═[ τ ]═► Q′) × Rel (M ∖ hidden blkA) Q′)
pack r (r′ , Meq , pe , j′) =
    SpecOf r , wτ τ*-refl
  , (r′ , cong (λ z → z ∖ hidden blkA) Meq , cong procOf (sym pe) , j′)

------------------------------------------------------------------------
-- §A4  *** (P6) DISCHARGED *** — the `break` inversion's own `broken`-bit
-- update, from the base layer's widened `PES.break-invert`.
--
-- The medium's break successor is named by TWO pointwise-equal but syntactically
-- distinct update functions: the route layer's `SR.broken-upd` (a `with j ≟ l`
-- function, which is what the inversion builds) and the coupling's `brkSet` (an
-- `if ⌊ l ≟ j ⌋` term, which is what the coupling's whole-map flag lemma
-- `LiveSpecCouple.specPos-break` reads).  There is no function extensionality in
-- this development, so the two are bridged ONE LINK AT A TIME and the coupling
-- lemma is consumed in its pointwise form (`specPos-break′`, the only one this
-- module imports) — which loses nothing, since `specPos` reads the bit map at
-- only the four link keys.
------------------------------------------------------------------------

-- `SR.broken-upd brk l` and `brkSet l brk` agree at every link: both scrutinise
-- the same decision, in opposite orders (`j ≟ l` versus `l ≟ j`), so the two
-- `with` columns reduce both sides simultaneously
bupd≡brkSet : (brk : Link → Bool) (l j : Link)
            → SR.broken-upd brk l j ≡ brkSet l brk j
bupd≡brkSet brk l j with l ≟ j | j ≟ l
... | yes refl | yes _  = refl
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | no  ¬p   | yes q  = ⊥-elim (¬p (sym q))
... | no  _    | no  _  = refl

-- (P6) THE THEOREM: at the `break` inversion's own successor the `broken` map is
-- the coupling's `brkSet` of the fired link — pointwise.  The whole-map form is
-- NOT derivable (that is exactly the funext gap); the pointwise instance is, by
-- `cong (λ f → f j)` on the inversion's fifth field followed by the bridge.
brkBits : (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
        → (step : radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M)
        → (j : Link)
        → broken (proj₁ (PES.break-invert r l₀ step)) j
          ≡ brkSet l₀ (broken (med (toSys r))) j
brkBits r l₀ step j =
  trans (cong (λ f → f j)
           (proj₂ (proj₂ (proj₂ (proj₂ (PES.break-invert r l₀ step))))))
        (bupd≡brkSet (broken (med (toSys r))) l₀ j)

------------------------------------------------------------------------
-- §A5  *** (P7) DISCHARGED *** — the ⁺ cone's own producer landing.
--
-- The diagnosis in the old premise block was right: `LiveLegApiCone.srvUp-of`
-- built the generic landing (`SrvLands l hi e a bfs′`, "a `sendBFBlock` at the
-- slot's own key lands the sent block here") and consumed it only to make the
-- `blkA`-specialised, crossing-gated `VisLeaves⁺.vProdSend`, dropping the generic
-- form together with the server-FIXED arm's `IsSBB → ⊥`.  The fix is the one the
-- diagnosis named: KEEP it.  `SrvUpFacts` gained the landing as a seventh
-- component, `NodeAApiEvo` gained the FIRED-LINK pin its own peels already took
-- as an argument (that is what refutes the CO-leg, which was the one genuinely
-- undecidable case), and `driverExpose⁺` now reports the landing per leg —
-- vacuously on the three non-A node arms, where no `sendBFBlock` on `linkAB`/
-- `linkAC` is possible at all.  NO base module was touched: every witness was
-- already inside `LiveLegApiCone`.
--
-- The premise is recovered by ONE application, at the concrete kept label: the
-- `SbbAt` hypothesis at the leg's own key IS `refl` there.
------------------------------------------------------------------------

-- (P7) THE THEOREM: A's kept produce LANDS the block in the leg's upstream BF
-- server, at the ⁺ cone's own successor
prodLands : (r : RState) (l : TwoLegs) {a : Block₃} {M : NetProc}
          → (apimem : apiES .mem
               (Block₃ , apiBF (upLinkOf l) hi sendBFBlock) a)
          → (ns : absNodesOf (toSys r)
               ─[ ev (evl (evLabel Block₃
                    (apiBF (upLinkOf l) hi sendBFBlock) a)) ]─► M)
          → upSrv l (deSucc (driverExpose⁺ (toSys r) apimem ns)) ≡ bsBlk1 a
prodLands r l {a} apimem ns =
  driverExpose⁺-prodLands l (toSys r) apimem ns a refl

------------------------------------------------------------------------
-- §A6  *** (P8) DISCHARGED *** — the ⁺ cone's own consumer landing.
--
-- The gate's two findings were both right and both had to be answered.  (i) The
-- CONTENT was already in the cone's output: `ldCons`' `ConsAdv` has exactly one
-- edge out of `cp3` (`c34`), so the successor phase is `cp4` and `pastRecv` is
-- `refl` there.  (ii) But two things were projected away — the SESSION-40
-- anchor's `≡ cp3` GATE and, worse, the FIRED LINK, without which the co-leg's
-- `ldFix` arm is not merely unproved but *unrefutable* (`absNodeD-fp` says only
-- "consumer on BD or CD").
--
-- Both come from ONE witness the node-D peel already had and dropped: the firing
-- consume driver's own step.  Owner grant #5 makes `NodeDDrv` carry it (one
-- trailing field per constructor, every existing field untouched);
-- `LiveLegApiCone` §1b and `LiveLegApiExpose` §9b then read the gate off it by a `recvBFBlock` table
-- inversion and the link by `decConsD-ev-link`, and reports the landing per leg.
--
-- The premise is recovered by ONE application plus ONE `cong`: the cone states
-- the phase as `≡ cp4` (so that the cone needs no import of the coupling) and
-- `pastRecv cp4` is `true` by definition.
------------------------------------------------------------------------

-- (P8) THE THEOREM: D's kept receive LANDS the block in the leg's consume slot,
-- past the receive threshold, at the ⁺ cone's own successor
recvLands : (r : RState) (l : TwoLegs) {a : Block₃} {M : NetProc}
          → (apimem : apiES .mem
               (Block₃ , apiBF (linkOf l) hi recvBFBlock) a)
          → (ns : absNodesOf (toSys r)
               ─[ ev (evl (evLabel Block₃
                    (apiBF (linkOf l) hi recvBFBlock) a)) ]─► M)
          → (pastRecv (phOf l (deSucc (driverExpose⁺ (toSys r) apimem ns))) ≡ true)
            × (cblkOf l (deSucc (driverExpose⁺ (toSys r) apimem ns)) ≡ a)
recvLands r l {a} apimem ns
  with driverExpose⁺-recvLands l (toSys r) apimem ns a refl
... | ph4 , cbl = cong pastRecv ph4 , cbl

------------------------------------------------------------------------
-- §2/§3/§4/§7 — the obligations, under the premise block.
--
-- `Sim`'s THREE parameters are exactly (P2)-(P4) of the header's audit — (P5),
-- (P6), (P7) and (P8) left the telescope when §4, §A4, §A5 and §A6 discharged
-- them, and (P1) `cellCp3` left it at the cellCp3 window (`LiveChanJoin` §5e) — in
-- the order of the campaign's decisions.  (SUPERSEDED IN PLACE: this read "FOUR
-- parameters … (P1)-(P4)".)  Each is stated at the type its supplier
-- exports, so instantiation is by name and Agda checks the wiring.
------------------------------------------------------------------------

module Sim
  -- *** (P1) `cellCp3` — GONE FROM THIS TELESCOPE (the cellCp3 window, slice D). ***
  -- It read `(cellCp3 : (l : TwoLegs) (b : Block₃) (r : RState) → LS.CellCp3 l b r)`
  -- and was the assembly's single premise, consumed only by the io READ class and so
  -- only by `FwdT`/`FwdE`.  It is now a THEOREM — `LiveChanJoin.cellCp3-of`, off the
  -- CARRIED join (`ChanLeg` plus `UpJoint`'s and `BFJoint`'s third members) — and the
  -- assembly takes it on the READ class's preservation MAP, so `LiveChanJoin` supplies
  -- it inside its own arm and nothing reaches here.  The parked
  -- `LiveTokenExcl.cellCp3-of` route (the two chain alignments) was NOT the one taken:
  -- see `LiveChanJoin` §5e.  *** With it goes the LAST `Premises` field, so
  -- `LivenessProof.Premises` is EMPTY and `livenessSpec` is UNCONDITIONAL. ***

  -- (P2)/(P3) the six in-flight positions per leg, at every reachable config
  -- (owner decision #5).  Supplier: `LivenessProof.At.ifo-of`, which now BUILDS
  -- both records — the four cell/server fields off the channel invariant
  -- (`LiveChanInv`/`LiveSrvOpen`) and the two api fields off `LiveRelayCS`, which
  -- since T11h needs NO residual at all: `CSAt` and `BFAt` are `⊤` at all seventeen
  -- shapes, so `ifo-of` is a function of the CARRIED join alone and takes no
  -- `Premises` argument (T12 deleted the last one, `bfRes`).
  -- (SUPERSEDED IN PLACE, one of §0's two drift sites: this read "the two api fields
  -- off the split residual (`LiveRelayCS`)" — the "split" residual was `csRes`/`bfRes`,
  -- retired at T8c-iii and T12.)
  --
  -- *** THE CARRIED INVARIANT IS AN ARGUMENT OF THE SUPPLIER (Task 4). ***  Eight
  -- of the twelve facts are THEOREMS, and their premises include `NoTwoTokens` —
  -- a PROVED conjunct of the `Rel`'s own `LegJointB` (`LiveTokenExcl`), not
  -- something a ∀-`RState` supplier could invent.  So the two parameters take the
  -- invariant at the very config they answer about; `stabR` below has it in hand
  -- (it is the `Rel`'s fourth component) and passes it on.
  --
  -- *** AND BOTH HOPS' CHANNEL HALVES NOW COME OFF THAT SAME ARGUMENT (the join,
  -- LANDED — the up hop at task 4, the down hop at task 5). ***  `Rel`'s fourth
  -- component is `LCJ.LegJointUB`, not `LA.LegJointB` — this module DID change for it,
  -- at 16 type sites plus two consumer projections (`stabR` and `sqrt-⊥` take
  -- `LCJ.legJointB-of` to reach the assembly's own product) — and
  -- `LivenessProof.Premises` accordingly carries NO channel field at all.  Task 5
  -- widened the carried factor from `ChanUp` to the whole `ChanLeg` and this module did
  -- NOT change again: `ChanLeg` is itself a product and the factor is still trailing.
  -- What has never changed is any obligation here: `LegJointUB` is strictly stronger, so
  -- every arm's map and `rel-init` discharge more, and no premise of
  -- `fwdT`/`fwdE`/`stabR` weakened.
  (ifoBD : (r : RState) → LCJ.LegJointUB legBD (toSys r) → InFlightOpen legBD r)
  (ifoCD : (r : RState) → LCJ.LegJointUB legBD (toSys r) → InFlightOpen legCD r)

  -- (P4) divergence-freedom of the hidden abstraction.  A THEOREM, not an
  -- assumption: `LiveNoDivH.Descent.noDivH` (`LiveNoDivH.agda:376-377`) at that
  -- module's six banked parameters.  Taken as ONE abstract fact rather than by
  -- threading `(μTot, μτ, τreflect, liftτ*-μ, hidEv-μ, liftReach-ev)`, because
  -- the six would put this module's closure on the heavy `LTL/Walk/*` suffix for
  -- no gain — `LiveHeavyFacts` opens `Descent` (the descent is ANCHORED, so the
  -- τ side is the banked `τreflect` plus `liftτ*-μ`, not a merged reflector) and
  -- `LivenessProof` passes `noDivH` on by name.
  (noDivH : (r : RState) → Diverges (radec r ∖ hidden blkA) → ⊥)

  -- *** THE THREE KEPT-CLASS SUCCESSOR FACTS OF INSTALMENT 3 ARE ALL
  -- THEOREMS NOW — none of them is a parameter here any more. ***
  --
  -- Each kept class owed a component-level equation AT THE INVARIANT ARM'S OWN
  -- SUCCESSOR, and the frozen inversions PROJECTED EXACTLY THOSE AWAY:
  --
  --   · the `break` arm's successor medium is `proj₁ (break-invert …)`.
  --     `break-invert` was widened to carry the `broken`-bit update it always
  --     built (`mkMed (phase m) (broken-upd (broken m) i)`) by binding
  --     `link-break-chan`'s `i ≡ l₀` pin instead of discarding it, and §A4's
  --     `brkBits` is the resulting fact.  The recorded reason no consumer could
  --     recover it stands and is why the widening was the only route: the peel
  --     does not reduce for a variable step (§B's mechanical note) and `decMed`
  --     is NOT injective (a broken link decodes to `Skip` whatever its phase);
  --   · the api arm's successor is the ⁺ cone's own `s′`, and the cone reports
  --     the firing driver as a FOUR-ARM DISJUNCTION (`LegDriverStep`) in which
  --     `ldFix` — "the event fired elsewhere, this leg is entirely fixed" — is
  --     type-consistent with EVERY label.  Which arm holds was decided inside
  --     `driverExpose⁺` by the node peel and then forgotten.  The PRODUCE half is
  --     §A5's `prodLands` (the cone now KEEPS the generic `SrvLands` and exports
  --     node A's fired-link pin — no base module touched); the RECEIVE half is
  --     §A6's `recvLands`, on owner grant #5: `NodeDDrv` carries the firing
  --     consume driver's own step, off which the `cp3` gate and the fired link
  --     both follow inside `LiveLegApiCone`.
  --
  -- All three were TRUE by the very peels that build the successors, and each is
  -- stated at the exact term the arm's successor δ-reduces to, so the composition
  -- stayed definitional throughout — no `subst` appears in §D, and the two `refl`
  -- probes at its head still typecheck.
  where

  ------------------------------------------------------------------------
  -- §2  `stabR` — SLOTTED, and the shapes really do match.
  --
  -- `LiveStableOffer.StabOffer r` is `isStable (radec r ∖ hidden blkA) → Settle
  -- (SpecOf r) (radec r ∖ hidden blkA)` (`:671-673`) and `Settle q p` is
  -- `Σ[ q′ ] ((q ─[τ*]─► q′) × isStable q′ × (∀ e → Offers q′ e → Offers p e))`
  -- (`:588-591`).  `FSimFromRel`'s `stabR` field (`BisimFromRel:103-107`) is
  -- `Rel p q → isStable p → Σ[ q′ ] ((q ─[τ*]─► q′) × isStable q′ × (∀ (e :
  -- Event√ R) → Offers q′ e → Offers p e))`.  With both decode equations matched
  -- to `refl`, `p` IS `radec r ∖ hidden blkA` and `q` IS `SpecOf r`, so the two
  -- Σ-types are the same type — verified by this definition typechecking with no
  -- `subst`, which was the point of stating `Settle` in the FSim's coordinates.
  -- The `Event√` argument is at `R = ⊤ {0ℓ}` on both sides (the whole-system
  -- return type, `SysReach.NetProc`).
  ------------------------------------------------------------------------

  -- the FSim's stability obligation, from the campaign's closing theorem
  stabR : ∀ {P Q} → Rel P Q → isStable P
        → Σ[ Q′ ∈ SpecProc ]
            ( (Q ─[τ*]─► Q′)
            × isStable Q′
            × (∀ (e : Event√ (⊤ {0ℓ})) → Offers Q′ e → Offers P e) )
  stabR (r , refl , refl , j) st =
    stabR-final r (LCJ.legJointB-of (toSys r) j) (ifoBD r j) (ifoCD r j) st

  ------------------------------------------------------------------------
  -- §3  `ndivL` — SLOTTED.  The `Rel`'s impl equation is exactly the rewrite the
  -- brief predicted, and matching it to `refl` performs it, so `noDivH` applies
  -- at the config the relation carries.  The divergence axis needs nothing new.
  ------------------------------------------------------------------------

  -- the FSim's divergence obligation: the implementation never livelocks
  ndivL : ∀ {P Q} → Rel P Q → Diverges P → ⊥
  ndivL (r , refl , _ , _) d = noDivH r d

  ------------------------------------------------------------------------
  -- §4  THE `√` ARM (booked gap G3) — and the STRUCTURAL FINDING it produced.
  --
  -- *** THE ANALYSIS BELOW IS HISTORICAL — (P5) IS NOW DISCHARGED, right here in
  -- `sqrt-⊥`. ***  Its diagnosis stands verbatim (the refutation had to come from
  -- the NODES, via the KA/TS/LN/LF inertness of `NodeSpecs:165-171`, and that is a
  -- reachability invariant); only its "not funded here" pricing is out of date.
  -- OUTCOME: funded on owner grant #6 — `PipeNodeIoEvo` gained the third abstract
  -- fact family that transports a bundle's `InertPos` answer to the top, the
  -- conjunct joined `LegJointB` (`LiveLegAssembly:657`), and the ladder is
  -- `LiveRetFree` (eight banked `SysSqrt` rungs).  ACTUAL: 328 net non-comment
  -- lines against the band 180-350 quoted below as 150-250 + 150-350 — i.e. the
  -- estimate's magnitude was right and its split was not (the ladder came in at
  -- ~75, the carriage at ~253).
  --
  -- `fwdE` quantifies over `l : Event√ R`, so the `√ x` case is an obligation.
  -- `Hide-ev-elim` (`TraceLawsHide:248-252`) splits a visible step of `P ∖ A`
  -- into `heV` (a KEPT event of `P`) and `he√` (`:232`), whose whole content is
  -- `force P ≡ ret x` with target `deadlock`.  At `P = radec r` that is `noRetA`.
  --
  -- WHY THIS IS A PREMISE AND NOT A ONE-LINE REFUTATION — re-derived, and it
  -- contradicts the brief's item 9 in both halves:
  --   · The brief's refutation route is `WalkBrkFire.unb-ret-⊥`
  --     (`WalkBrkFire.agda:298-303`), which refutes `force (absDec s) ≡ ret` FROM
  --     AN UNBROKEN LINK (it fires the break offer and reads off a `react`).  Its
  --     hypothesis `broken (med s) l ≡ false` is available on the WALK, where the
  --     confinement `Unb` (`:322`) supplies it — but the FSim quantifies over ALL
  --     reachable configs, including the all-links-broken ones, and there
  --     `decLink l ph true = Skip` (`SysMedium:155`), whose force IS a `ret`.  So
  --     the medium itself stops blocking the `√` and the refutation must come
  --     from the NODES.
  --   · The abstract `√` is not vacuous by construction either: `SysBisim`
  --     HANDLES it rather than refuting it (`osqrtB-impl`, `:1000-1003`, via
  --     `sys-wret`), and `SysSqrt` exists precisely to transfer `ret`s.
  --   · Nor can the arm be HANDLED on the spec side: `LSpec`/`Prod`/`Done`/`Stop`
  --     are all `react` nodes (`Spec.lagda.md:311` and its siblings), so no spec
  --     state can `√`, and `LiveStableOffer` refutes spec `√`s by the absurd
  --     pattern `sRet ()` (`:605`, `:654`).  A `√`-ing implementation would
  --     FALSIFY the refinement, so the arm MUST be refuted.
  --   · The true refutation is the KA/TS/LN/LF INERTNESS recorded in as many
  --     words at `NodeSpecs.agda:165-171` ("the node drivers never offer
  --     `apiKA`, so KA is INERT (frozen at `kcClient`)"): `kaCfin kcTerm/kcTermE`
  --     are the only `true` rows (`NodeSpecs:185-188`), and the abstract KA
  --     client sits at `kac ip` for a STATE field `ip : InertPos`
  --     (`SysStep:750-758`), so freezing it is a REACHABILITY invariant of the
  --     same kind as `InFlightOpen` — not a definitional fact.
  --   · PRICE of discharging it (recommended as a separate slice, not funded
  --     here): the `ret`-ladder peel `force (radec r) ≡ ret ⇒ that peer rets` is
  --     ~150-250 on `SysSqrt`'s banked rungs (`fHide-ret-inv`, `∥⇙-ret-inv`,
  --     `Par⊤-ret-inv`, `bundleG-wret`'s 12-deep `⦀` chain), plus an
  --     inert-freeze invariant carried in the `Rel` at ~150-350 (four step
  --     classes; the io class DOES move inert peers, so it is not a frame).
  --   · *** INSTALMENT 2, the gate's free NARROWING: the premise takes the
  --     `Rel`'s OWN invariant `LegJointB legBD (toSys r)`. ***  Re-derived at
  --     point of use: `LegInv l s = Σ[ b ] Σ[ k ] AtPos l k b s`
  --     (`LiveLegInv:456`) and NINE of the ten `AtPos` clauses (`:425-445`) pin
  --     `InCp03 (phOf l s)` or `ConsCp3 (phOf l s)` — i.e. node D's consumer
  --     sits at `cp0..cp3`, where `decConsD l (consD b ph) = decCons l hi b ph
  --     >> Skip` (`SysNode:972-973`) is `⟶`-headed and cannot force to `ret`
  --     (only `decCons … cp6 = Ret b`, `SysNode:958`, can, and it is reachable
  --     ONLY from the `lpDone` clause `:444-445`, whose phase conjunct is
  --     `ConsRecv`).  So the discharge owes the `ret` refutation at ONE token
  --     position instead of at every config: strictly smaller, and free here
  --     because every call site already holds the invariant.
  ------------------------------------------------------------------------

  -- a `√` of the doubly-hidden abstraction is impossible: `he√` pins it to a
  -- `ret` of `radec r`, which no reachable config carrying the joint invariant is
  sqrt-⊥ : (r : RState) → LCJ.LegJointUB legBD (toSys r)
         → {x : ⊤ {0ℓ}} {P′ : NetProc}
         → (radec r ∖ hidden blkA) ─[ ev (√ x) ]─► P′ → ⊥
  sqrt-⊥ r j step with TLH.Hide-ev-elim (hidden blkA) (radec r) step
  -- (the join) `noRetA-lit` reads the ASSEMBLY's product, so the carried invariant
  -- is projected — the review's caveat, paid on the CONSUMER side, so `LiveRetFree`
  -- itself is untouched
  ... | TLH.he√ eqf = LRF.noRetA-lit r (LCJ.legJointB-of (toSys r) j) eqf

  ------------------------------------------------------------------------
  -- §5/§6  THE TWO OBLIGATION TYPES (`FwdT` DISCHARGED IN §B BELOW).
  --
  -- Stated here — rather than left as prose — so that each instalment has a
  -- target Agda checks.  BOTH ARE NOW INHABITED: `fwdT : FwdT` is §B (instalment
  -- 2, at `cellCp3` and nothing else) and `fwdE : FwdE` is §D (instalment 3, at
  -- `cellCp3` and (P7)-(P8)) — and since the cellCp3 window at NOTHING, `cellCp3`
  -- being a theorem inside `LiveChanJoin` — so `Assemble` takes no obligation at all.  Both
  -- types are the corresponding `FSimFromRel` field with
  -- `Rel` substituted, transcribed from `BisimFromRel:99-102` — a mismatch here
  -- is a type error at §7's module application, which is exactly where it should
  -- surface, and §B typechecking against `FwdT` is what certifies the fit.
  ------------------------------------------------------------------------

  -- the τ obligation: an implementation τ is matched by a weak spec τ-move
  FwdT : Set₁
  FwdT = ∀ {P Q P′} → Rel P Q → P ─[ τ ]─► P′
       → Σ[ Q′ ∈ SpecProc ] ((Q ═[ τ ]═► Q′) × Rel P′ Q′)

  -- the visible obligation: an implementation visible step (`Event√`, so the `√`
  -- class is included and discharged by §4) is matched by a weak spec move
  FwdE : Set₁
  FwdE = ∀ {P Q} {l : Event√ (⊤ {0ℓ})} {P′} → Rel P Q → P ─[ ev l ]─► P′
       → Σ[ Q′ ∈ SpecProc ] ((Q ═[ ev l ]═► Q′) × Rel P′ Q′)

  ------------------------------------------------------------------------
  -- §B  *** `FwdT` — THE τ OBLIGATION, DISCHARGED. ***
  --
  -- `Hide-τ-elim` (`TraceLawsHide:219-225`) splits a τ of `radec r ∖ hidden blkA`
  -- into a TRUE τ of `radec r` (`hτP`) and a HIDDEN VISIBLE event of `radec r`
  -- (`hτH`, carrying `keptB blkA (X , e) a ≡ false` — the `hidden` record's `mem`
  -- field is that equation by definition).  Both arms then need the SAME two
  -- things, packaged as `StepOut` (§A): the invariant successor, and "the spec
  -- stays put".
  --
  -- WHICH THEOREMS THIS CONSUMES, AND THE ONE DEVIATION FROM THE CHARTER'S G1.
  -- G1 says: consume the `LegJointB`-level `tauStepB`/`evStepB`, not the weak fold
  -- and not the `LegJoint`-level `tauStepJ`/`evStepJ`.  This section consumes the
  -- `LegJointB` level as instructed, but ONE LEVEL BELOW THE LABEL SWITCH: the
  -- class arms `τpreserveB-med` / `tauIoB-in` / `tauIoB-out` / `evStepB-api`,
  -- which are precisely what `tauStepB` (`LiveLegAssembly:1197`) and `evStepB`
  -- (`:1002`) dispatch to.  *** THE REASON IS MECHANICAL AND WORTH RECORDING. ***
  -- `tauStepB` is defined by `with reflect-absDec-τ (toSys r) stp`, so
  -- `proj₁ (tauStepB … r stp)` is a `with`-generated application whose
  -- scrutinee is a NEUTRAL term for a variable `stp`: it does not reduce, and no
  -- `with` in a CONSUMER can unstick it (the scrutinee is not a subterm of the
  -- consumer's goal, so `with` cannot abstract it).  A flag proof must name the
  -- successor's components, so the consumer has to re-do the label dispatch — and
  -- then it must call the arms, because calling the dispatcher as well would name
  -- a SECOND successor (the F2 existential-successor rule).  The dispatch below is
  -- therefore a transcription of `tauStepB`'s and `evStepB`'s own, and the
  -- *** keep-in-sync directive is exactly that: if either dispatcher's class
  -- table moves, this one must move with it. ***
  ------------------------------------------------------------------------

  -- the MEDIUM-DRAIN class.  `drainSucc` (`PipeTauMed:87-91`) rebuilds only the
  -- medium's cell phases: `broken` and all four node states are LITERALLY the
  -- source's, so every reader of the coupling is fixed by computation and the
  -- `refl` below is the whole flag proof.
  fwdT-med : (r : RState) → LCJ.LegJointUB legBD (toSys r) → {M M′ : NetProc}
           → decMed (med (toSys r)) ─[ τ ]─► M′
           → M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES)
           → StepOut r M
  fwdT-med r j ms Meq =
    let (r′ , Meq′ , pres) = LCJ.τpreserveU-med r ms Meq
    in  r′ , Meq′ , refl , pres j

  -- the io-SYNC FILL class (`input`).  G2 is FREE here, as the gate verified: the
  -- PAIRED cone `top-nodes-io-evoP⁺` (`LiveLegIoCone:801-813`) returns `med s ≡
  -- med s′` AND all four node readers' equations, and the arm's successor keeps
  -- the source's `broken` bits by construction (`m′`'s second field).  The cone
  -- call here is the SAME APPLICATION the arm makes, so it is the same successor.
  fwdT-io-in : (r : RState) → LCJ.LegJointUB legBD (toSys r)
             → (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               {M₁ N₁ M : NetProc}
             → (iomem : ioES .mem (Payload , input l₀ d₀ id₀) x)
             → decMed (med (toSys r))
                 ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► M₁
             → (sN : absNodesOf (toSys r)
                 ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► N₁)
             → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
             → StepOut r M
  fwdT-io-in r j l₀ d₀ id₀ x {N₁ = N₁} iomem sM sN Meq =
    let (r′ , Meq′ , pres) = LCJ.tauIoU-in r l₀ d₀ id₀ x iomem sM sN Meq
        (_ , _ , _ , _ , _ , _ , epAB , epAC , _ , _ , edBD , edCD , _)
          = top-nodes-io-evoP⁺ (toSys r) {Payload} {input l₀ d₀ id₀} {x} {N₁} iomem sN
    in  r′ , Meq′
      , specPos-of r (toSys r′) refl (cong pastSend (sym epAB))
          (cong pastSend (sym epAC))
          (cong₂ _∨_ (cong recvOf (sym edBD)) (cong recvOf (sym edCD)))
      , pres j

  -- the io-SYNC READ class (`output`) — the same, at §7's read arm
  fwdT-io-out : (r : RState) → LCJ.LegJointUB legBD (toSys r)
              → (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                {M₁ N₁ M : NetProc}
              → (iomem : ioES .mem (Payload , output l₀ d₀ id₀) x)
              → decMed (med (toSys r))
                  ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► M₁
              → (sN : absNodesOf (toSys r)
                  ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► N₁)
              → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
              → StepOut r M
  fwdT-io-out r j l₀ d₀ id₀ x {N₁ = N₁} iomem sM sN Meq =
    let (r′ , Meq′ , pres) = LCJ.tauIoU-out r l₀ d₀ id₀ x iomem sM sN Meq
        (_ , _ , _ , _ , _ , _ , epAB , epAC , _ , _ , edBD , edCD , _)
          = top-nodes-io-evoP⁺ (toSys r) {Payload} {output l₀ d₀ id₀} {x} {N₁} iomem sN
    in  r′ , Meq′
      , specPos-of r (toSys r′) refl (cong pastSend (sym epAB))
          (cong pastSend (sym epAC))
          (cong₂ _∨_ (cong recvOf (sym edBD)) (cong recvOf (sym edCD)))
      , pres j

  -- THE io LABEL DISPATCH: only `input`/`output` are in `ioES`, so the other
  -- fourteen constructors are refuted by the membership witness itself
  -- (`LiveLegAssembly.tauIoB`'s table, transcribed — keep in sync)
  fwdT-io : (r : RState) → LCJ.LegJointUB legBD (toSys r)
          → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
          → ioES .mem (X , e) a
          → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁
          → absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁
          → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
          → StepOut r M
  fwdT-io r j {e = input  l₀ d₀ id₀} {a = x} iomem sM sN Meq =
    fwdT-io-in  r j l₀ d₀ id₀ x iomem sM sN Meq
  fwdT-io r j {e = output l₀ d₀ id₀} {a = x} iomem sM sN Meq =
    fwdT-io-out r j l₀ d₀ id₀ x iomem sM sN Meq
  fwdT-io r j {e = sndmsg _ _ _} ()
  fwdT-io r j {e = rcvmsg _ _ _} ()
  fwdT-io r j {e = tx     _ _ _} ()
  fwdT-io r j {e = sndack _ _ _} ()
  fwdT-io r j {e = rcvack _ _ _} ()
  fwdT-io r j {e = ack    _ _ _} ()
  fwdT-io r j {e = done   _ _ _} ()
  fwdT-io r j {e = apiCS  _ _ _} ()
  fwdT-io r j {e = apiBF  _ _ _} ()
  fwdT-io r j {e = apiTS  _ _ _} ()
  fwdT-io r j {e = apiKA  _ _ _} ()
  fwdT-io r j {e = apiLN  _ _ _} ()
  fwdT-io r j {e = apiLF  _ _ _} ()
  fwdT-io r j {e = break  _}     ()

  -- THE TRUE-τ ARM: a hidden τ of the abstraction is a medium drain or an io
  -- SYNC; `absNodesOf` has no autonomous τ (`absNodesOf-no-τ`).  Dispatch
  -- transcribed from `LiveLegAssembly.tauStepB` (`:1221-1227`) — keep in sync.
  fwdT-τ : (r : RState) → LCJ.LegJointUB legBD (toSys r) → {M : NetProc}
         → radec r ─[ τ ]─► M → StepOut r M
  fwdT-τ r j stp with reflect-absDec-τ (toSys r) stp
  ... | innerτ P′ innerStep Peq
      with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
  ...   | medτ   M′ ms eqP = fwdT-med r j ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
  ...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
  fwdT-τ r j stp | hidSync M₁ N₁ iomem sM sN Peq = fwdT-io r j iomem sM sN Peq

  -- THE HIDDEN api CLASS (`apiCS` / non-kept `apiBF` / `done`) — the one class
  -- whose drivers really do move, and the campaign's flagged risk.  The invariant
  -- comes from `evStepB-api`; the flags from §A3 at the SAME successor, fed the
  -- `SrvCoupled` half of the invariant the `Rel` carries (`LegJoint`'s `PipeInvS`
  -- is `PipeInv⁺ × SrvCoupled`, `PipeInvProd:109-110`, so it is a `proj₂`) and the
  -- cone outputs of the SAME `driverExpose⁺` application the arm peels.
  fwdT-api : (r : RState) → LCJ.LegJointUB legBD (toSys r)
           → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
           → (aic : IsApiCSBF e) (apimem : apiES .mem (X , e) a)
           → keptB blkA (X , e) a ≡ false
           → radec r ─[ ev (evl (evLabel X e a)) ]─► M
           → StepOut r M
  fwdT-api r j aic apimem hid step =
    let (r′ , Mr , pres) = LCJ.evStepU-api r aic apimem step
        (N₁ , ns , _) = LA.api-nodes-solo r aic step
        -- (T3b) the cone's report is a RECORD: every slot below is read BY NAME
        de = driverExpose⁺ (toSys r) apimem ns
    in  r′ , Mr
      , apiSpecFix r (deSucc de) hid (deMed de)
          (proj₂ (proj₁ (proj₁ (j legBD)))) (proj₂ (proj₁ (proj₁ (j legCD))))
          (deLdBD de) (deLdCD de) (deVlBD de) (deVlCD de) (deLvBD de) (deLvCD de)
      , pres j

  -- THE HIDDEN VISIBLE DISPATCH.  `break` is KEPT (`keptB _ (_ , break _) _ =
  -- true`), so the hidden-membership witness refutes it OUTRIGHT; io is refuted by
  -- `oevB-no-io`; the four inert api classes and the six wire classes by
  -- `oevB-refute` — the same twelve clause heads `evStepB` (`:1020-1046`) has,
  -- transcribed (keep in sync).
  fwdT-vis : (r : RState) → LCJ.LegJointUB legBD (toSys r)
           → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
           → keptB blkA (X , e) a ≡ false
           → radec r ─[ ev (evl (evLabel X e a)) ]─► M
           → StepOut r M
  fwdT-vis r j {e = apiCS l₀ d₀ m}  hid step = fwdT-api r j aicCS   tt hid step
  fwdT-vis r j {e = apiBF l₀ d₀ m}  hid step = fwdT-api r j aicBF   tt hid step
  fwdT-vis r j {e = done  l₀ d₀ id} hid step = fwdT-api r j aicDone tt hid step
  fwdT-vis r j {e = break l₀}       ()
  fwdT-vis r j {e = input  l₀ d₀ id} hid step = ⊥-elim (oevB-no-io r tt step)
  fwdT-vis r j {e = output l₀ d₀ id} hid step = ⊥-elim (oevB-no-io r tt step)
  fwdT-vis r j {e = apiKA l₀ d₀ m} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-apiKA (med (toSys r)))
             (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
  fwdT-vis r j {e = apiTS l₀ d₀ m} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-apiTS (med (toSys r)))
             (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
  fwdT-vis r j {e = apiLN l₀ d₀ m} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-apiLN (med (toSys r)))
             (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
  fwdT-vis r j {e = apiLF l₀ d₀ m} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-apiLF (med (toSys r)))
             (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
  fwdT-vis r j {e = sndmsg l₀ d₀ id} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-sndmsg (med (toSys r)))
             (SR.absnodes-no-sndmsg (toSys r)) step)
  fwdT-vis r j {e = rcvmsg l₀ d₀ id} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-rcvmsg (med (toSys r)))
             (SR.absnodes-no-rcvmsg (toSys r)) step)
  fwdT-vis r j {e = tx l₀ d₀ id} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-tx (med (toSys r)))
             (SR.absnodes-no-tx (toSys r)) step)
  fwdT-vis r j {e = sndack l₀ d₀ id} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-sndack (med (toSys r)))
             (SR.absnodes-no-sndack (toSys r)) step)
  fwdT-vis r j {e = rcvack l₀ d₀ id} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-rcvack (med (toSys r)))
             (SR.absnodes-no-rcvack (toSys r)) step)
  fwdT-vis r j {e = ack l₀ d₀ id} hid step =
    ⊥-elim (oevB-refute r (SR.medium-no-ack (med (toSys r)))
             (SR.absnodes-no-ack (toSys r)) step)

  -- *** THE τ OBLIGATION. ***  Both `Rel` decode equations are matched to `refl`
  -- (which is what instantiates `P`/`Q` to the decode terms), the outer hide is
  -- inverted once, and each arm returns a `StepOut` that `pack` turns into the
  -- FSim's answer.
  fwdT : FwdT
  fwdT (r , refl , refl , j) stp with TLH.Hide-τ-elim (hidden blkA) (radec r) stp
  ... | TLH.hτP M′ tstep refl     = pack r (fwdT-τ   r j tstep)
  ... | TLH.hτH M′ hid estep refl = pack r (fwdT-vis r j hid estep)

  ------------------------------------------------------------------------
  -- §D  *** `FwdE` — THE VISIBLE OBLIGATION, DISCHARGED. ***
  --
  -- `Hide-ev-elim` (`TraceLawsHide:249-252`) splits a visible step of
  -- `radec r ∖ hidden blkA` into `heV` (a KEPT event of `radec r`, carrying the
  -- NEGATED hidden-membership) and `he√` (a `ret` of `radec r`, §4's arm).  The
  -- kept arm dispatches on the label: `keptB` is a closed four-row alphabet, so
  -- the classes are the four `break`s, the two produces and the two receives —
  -- and NOTHING else is kept, which is what makes the remaining fourteen event
  -- constructors absurd against the kept-ness equation itself.
  --
  -- *** THE SUCCESSOR-IDENTITY COUPLING (the sync directive the gate asked
  -- for). ***  Every arm below proves its flag equations about the CONE's
  -- successor (`deSucc (driverExpose⁺ …)` / `proj₁ (break-invert …)`) and feeds
  -- them to a `specPos-*` lemma stated about the INVARIANT arm's `r′`.  That
  -- composes because `toSys r′` δ-REDUCES to that very state: `rcloseʷ` returns
  -- `mkR s′ …` (`SysReach:226`) and `RState.sys (mkR s′ _)` is `s′`, so the two
  -- coordinates are DEFINITIONALLY EQUAL and no `subst` appears anywhere in this
  -- section.  It is a CONVERSION, not a theorem, and nothing in the type of
  -- either arm records it — *** so if `evStepJ-api`/`evStepJ-break` ever stop
  -- building their successor from the peel this section repeats (a `with`, a
  -- helper, an extra `subst` inside the arm), every arm below breaks with an
  -- opaque `[UnequalTerms]`.  The two probes immediately below are the tripwire:
  -- they typecheck ONLY while the identity is definitional. ***
  ------------------------------------------------------------------------

  -- REGRESSION (the successor-identity coupling, api side): the visible api
  -- arm's `r′` and the ⁺ cone's `s′` are the SAME state, by conversion
  _ : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
      (aic : IsApiCSBF e) (apimem : apiES .mem (X , e) a)
      (step : radec r ─[ ev (evl (evLabel X e a)) ]─► M)
    → toSys (proj₁ (LCJ.evStepU-api r aic apimem step))
      ≡ deSucc (driverExpose⁺ (toSys r) apimem
                  (proj₁ (proj₂ (LA.api-nodes-solo r aic step))))
  _ = λ r aic apimem step → refl

  -- REGRESSION (the same coupling, break side): the `break` arm's successor
  -- medium IS the frozen inversion's own `m′`
  _ : (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
      (step : radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M)
    → med (toSys (proj₁ (LCJ.evStepU-break r l₀ step)))
      ≡ proj₁ (PES.break-invert r l₀ step)
  _ = λ r l₀ step → refl

  -- the FwdE answer at one kept step: the shape all three classes return
  KeptOut : (r : RState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
            (M : NetProc) → Set₁
  KeptOut r {X} e a M =
    Σ[ Q′ ∈ SpecProc ]
      ((SpecOf r ═[ ev (evl (evLabel X e a)) ]═► Q′) × Rel (M ∖ hidden blkA) Q′)

  -- THE KEPT `break` CLASS.  The medium is the ONLY component that moves — the
  -- arm's successor shares node A and node D LITERALLY (`evStepJ-break`'s
  -- `s′ = mkSys m′ (nA (toSys r)) …`), so the two node premises of
  -- `specPos-break′` are `refl` and the whole class is §A4's `brkBits` THEOREM
  -- plus the banked flag lemma plus the banked spec move.  The POINTWISE flag
  -- lemma is the one used — see §A4 for why the whole-map one is unreachable.
  fwdE-break : (r : RState) → LCJ.LegJointUB legBD (toSys r) → (l₀ : Link)
             → {a : ⊤₀} {M : NetProc}
             → (step : radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M)
             → KeptOut r (break l₀) a M
  fwdE-break r j l₀ step =
    let (r′ , Mr , pres) = LCJ.evStepU-break r l₀ step
        pe : specPos r′ ≡ brkPos l₀ (specPos r)
        pe = specPos-break′ l₀ r r′ (brkBits r l₀ step) refl refl
    in  procOf (brkPos l₀ (specPos r))
      , spec-break-move l₀ (specPos r)
      , (r′ , cong (λ z → z ∖ hidden blkA) Mr , cong procOf (sym pe) , pres j)

  -- THE KEPT PRODUCE CLASS (leg-indexed: `legBD` is the AB produce, `legCD` the
  -- AC one).  The firing leg's flag comes from (P7) through the invariant AT THE
  -- SUCCESSOR — `SrvCoupled` turns "the up server holds the block" into
  -- `ProdSent` — and the OTHER THREE readers from §C3 at the same cone peel: the
  -- co-leg's producer by the non-hidden threshold refutation (its up-link is not
  -- the fired one), both legs' consumers because the label is no `recvBFBlock`.
  fwdE-prod : (r : RState) → LCJ.LegJointUB legBD (toSys r) → (l : TwoLegs)
            → {a : Block₃} {M : NetProc} → a ≡ blkA
            → (step : radec r
                 ─[ ev (evl (evLabel Block₃
                      (apiBF (upLinkOf l) hi sendBFBlock) a)) ]─► M)
            → KeptOut r (apiBF (upLinkOf l) hi sendBFBlock) a M
  fwdE-prod r j l {a} eqa step =
    let (r′ , Mr , pres) = LCJ.evStepU-api r aicBF tt step
        (N₁ , ns , _)    = LA.api-nodes-solo r aicBF step
        -- (T3b) the cone's report is a RECORD: every slot below is read BY NAME
        de = driverExpose⁺ (toSys r) tt ns
        s′ = deSucc de
        medEq = deMed de
        j′ = pres j
        ldOf : (l′ : TwoLegs)
             → LegDriverStep l′ (toSys r) s′ (apiBF (upLinkOf l) hi sendBFBlock) a
        ldOf = pickLeg (deLdBD de) (deLdCD de)
        vlOf : (l′ : TwoLegs) → VisLeaves⁺ l′ (toSys r) s′
        vlOf = pickLeg (deVlBD de) (deVlCD de)
        lvOf : (l′ : TwoLegs)
             → LegValStep l′ (toSys r) s′ (apiBF (upLinkOf l) hi sendBFBlock) a
        lvOf = pickLeg (deLvBD de) (deLvCD de)
        scOf : (l′ : TwoLegs) → SrvCoupled l′ (toSys r)
        scOf = λ l′ → proj₂ (proj₁ (proj₁ (j l′)))
        -- the FIRING leg's flag: (P7) + `SrvCoupled` at the successor
        e1 : pastSend (prodOf l s′) ≡ true
        e1 = pastSend-sent (prodOf l s′)
               (proj₁ (proj₂ (proj₁ (proj₁ (j′ l))))
                  (subst BFsHasBlk (sym (prodLands r l tt ns)) tt))
        -- the CO-leg's produce reader, and both legs' delivery readers
        e2 : pastSend (prodOf (coLeg l) s′) ≡ pastSend (prodOf (coLeg l) (toSys r))
        e2 = prodFlag-at (coLeg l) (toSys r) s′
               (λ w → upLink-co-⊥ l (trans (cong sbbLink (cong (λ z →
                        evLabel Block₃ (apiBF (upLinkOf l) hi sendBFBlock) z) eqa))
                        w))
               (scOf (coLeg l)) (ldOf (coLeg l)) (vlOf (coLeg l)) (lvOf (coLeg l))
        ed : delivD (nD s′) ≡ delivD (nD (toSys r))
        ed = delivD-fix (toSys r) s′
               (recvFlag-at legBD (toSys r) s′ (λ ()) (ldOf legBD) (lvOf legBD))
               (recvFlag-at legCD (toSys r) s′ (λ ()) (ldOf legCD) (lvOf legCD))
        pe : specPos r′ ≡ setP l (specPos r)
        pe = specPos-prod l r r′ (cong broken (sym medEq)) e1 e2 ed
    in  procOf (setP l (specPos r))
      , subst (λ z → SpecOf r ═[ ev (evl (evLabel Block₃
                 (apiBF (upLinkOf l) hi sendBFBlock) z)) ]═►
                 procOf (setP l (specPos r)))
              (sym eqa) (spec-prod-move l (specPos r))
      , (r′ , cong (λ z → z ∖ hidden blkA) Mr , cong procOf (sym pe) , pres j)

  -- THE KEPT RECEIVE CLASS.  Delivery WINS in `mkPos`, so the successor's
  -- position is `posDone` and NOTHING else needs to be shown fixed — (P8) plus
  -- one banked flag lemma.  The work is on the SPEC side: the idle position has
  -- no receive edge, so the class owes `keptRecv⇒prod`, which §C4 reads off the
  -- invariant AT THE SUCCESSOR (past the receive the token is at `lpDone`) and
  -- §C3 transports back over the step (a receive is no `sendBFBlock`).
  fwdE-recv : (r : RState) → LCJ.LegJointUB legBD (toSys r) → (l : TwoLegs)
            → {a : Block₃} {M : NetProc} → a ≡ blkA
            → (step : radec r
                 ─[ ev (evl (evLabel Block₃
                      (apiBF (linkOf l) hi recvBFBlock) a)) ]─► M)
            → KeptOut r (apiBF (linkOf l) hi recvBFBlock) a M
  fwdE-recv r j l {a} eqa step =
    let (r′ , Mr , pres) = LCJ.evStepU-api r aicBF tt step
        (N₁ , ns , _)    = LA.api-nodes-solo r aicBF step
        -- (T3b) the cone's report is a RECORD: every slot below is read BY NAME
        de = driverExpose⁺ (toSys r) tt ns
        s′ = deSucc de
        j′ = pres j
        ldOf : (l′ : TwoLegs)
             → LegDriverStep l′ (toSys r) s′ (apiBF (linkOf l) hi recvBFBlock) a
        ldOf = pickLeg (deLdBD de) (deLdCD de)
        vlOf : (l′ : TwoLegs) → VisLeaves⁺ l′ (toSys r) s′
        vlOf = pickLeg (deVlBD de) (deVlCD de)
        lvOf : (l′ : TwoLegs)
             → LegValStep l′ (toSys r) s′ (apiBF (linkOf l) hi recvBFBlock) a
        lvOf = pickLeg (deLvBD de) (deLvCD de)
        (pr , cb) = recvLands r l tt ns
        dl : recvOf (consD (cblkOf l s′) (phOf l s′)) ≡ true
        dl = recvOf-set l s′ pr (trans cb eqa)
        pe : specPos r′ ≡ posDone
        pe = specPos-recvL l r r′ dl
        -- `keptRecv⇒prod`: `ProdSent` at the successor, then back over the step
        sent : pastSend (prodOf l (toSys r)) ≡ true
        sent = trans (sym (prodFlag-at l (toSys r) s′ (λ ())
                            (proj₂ (proj₁ (proj₁ (j l))))
                            (ldOf l) (vlOf l) (lvOf l)))
                     (legInv-sent l s′ (proj₁ (proj₂ (proj₁ (j′ l)))) pr)
    in  Done blkA
      , subst (λ z → SpecOf r ═[ ev (evl (evLabel Block₃
                 (apiBF (linkOf l) hi recvBFBlock) z)) ]═► Done blkA)
              (sym eqa) (spec-recv-move l r sent)
      , (r′ , cong (λ z → z ∖ hidden blkA) Mr , cong procOf (sym pe) , pres j)

  -- THE KEPT DISPATCH.  `keptB`'s four rows: every `break`, the two produce
  -- links at `hi` carrying `blkA`, the two receive links at `hi` carrying
  -- `blkA`, and NOTHING ELSE — the other six BF tags and the other fourteen
  -- channels are refuted by the kept-ness equation itself (`keptB … = false`).
  fwdE-kept : (r : RState) → LCJ.LegJointUB legBD (toSys r)
            → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
            → keptB blkA (X , e) a ≡ true
            → (step : radec r ─[ ev (evl (evLabel X e a)) ]─► M)
            → KeptOut r e a M
  fwdE-kept r j {e = break l₀} kt step = fwdE-break r j l₀ step
  fwdE-kept r j {e = apiBF l₀ d₀ sendBFBlock} {a} kt step
    with kept-prd-dir l₀ d₀ a kt
  ... | refl with kept-prd-link l₀ hi a kt
  ...   | inj₁ refl = fwdE-prod r j legBD (kept-prd-blk linkAB hi a kt) step
  ...   | inj₂ refl = fwdE-prod r j legCD (kept-prd-blk linkAC hi a kt) step
  fwdE-kept r j {e = apiBF l₀ d₀ recvBFBlock} {a} kt step
    with kept-rcv-dir l₀ d₀ a kt
  ... | refl with kept-rcv-link l₀ hi a kt
  ...   | inj₁ refl = fwdE-recv r j legBD (kept-rcv-blk linkBD hi a kt) step
  ...   | inj₂ refl = fwdE-recv r j legCD (kept-rcv-blk linkCD hi a kt) step
  fwdE-kept r j {e = apiBF _ _ sendBFRequestRange} ()
  fwdE-kept r j {e = apiBF _ _ sendBFClientDone}   ()
  fwdE-kept r j {e = apiBF _ _ sendBFStartBatch}   ()
  fwdE-kept r j {e = apiBF _ _ sendBFNoBlocks}     ()
  fwdE-kept r j {e = apiBF _ _ sendBFBatchDone}    ()
  fwdE-kept r j {e = apiBF _ _ reqBFRange}         ()
  fwdE-kept r j {e = apiCS  _ _ _} ()
  fwdE-kept r j {e = apiKA  _ _ _} ()
  fwdE-kept r j {e = apiTS  _ _ _} ()
  fwdE-kept r j {e = apiLN  _ _ _} ()
  fwdE-kept r j {e = apiLF  _ _ _} ()
  fwdE-kept r j {e = done   _ _ _} ()
  fwdE-kept r j {e = input  _ _ _} ()
  fwdE-kept r j {e = output _ _ _} ()
  fwdE-kept r j {e = sndmsg _ _ _} ()
  fwdE-kept r j {e = rcvmsg _ _ _} ()
  fwdE-kept r j {e = tx     _ _ _} ()
  fwdE-kept r j {e = sndack _ _ _} ()
  fwdE-kept r j {e = rcvack _ _ _} ()
  fwdE-kept r j {e = ack    _ _ _} ()

  -- *** THE VISIBLE OBLIGATION. ***  The `√` class is where (P5) `noRetA`
  -- finally BITES: `sqrt-⊥` (§4) is the only consumer of it, and this is the
  -- only consumer of `sqrt-⊥` — before `FwdE` existed the premise was DEAD.
  fwdE : FwdE
  fwdE (r , refl , refl , j) step
    with TLH.Hide-ev-elim (hidden blkA) (radec r) step
  ... | TLH.heV M′ ¬hid estep = fwdE-kept r j (bool-not-false _ ¬hid) estep
  ... | TLH.he√ eqf           = ⊥-elim (sqrt-⊥ r j step)

  ------------------------------------------------------------------------
  -- §7  *** THE CONCLUSION. ***
  --
  -- `rel→fsim` at the seeded pair, then `fsim→⊑FD`.  THE ARGUMENT ORDER IS THE
  -- WHOLE CONTENT, and it is re-derived here rather than trusted:
  --   `rel→fsim rel-init : FSim (⊤ {0ℓ}) (abstractSystem ∖ hidden blkA)
  --                             (LSpec blkA true true)`
  -- (`FSimFromRel` produces `FSim R p q` with `p` the IMPLEMENTATION,
  -- `BisimFromRel:86`), and `fsim→⊑FD : FSim R Q P → P ⊑FD Q`
  -- (`FailureSim:196`), so `Q := abstractSystem ∖ hidden blkA` and
  -- `P := LSpec blkA true true` — i.e. the spec refines INTO the implementation,
  -- which is the direction the statement wants.  Falsification: building the
  -- `FSim` the other way round must be REJECTED (recorded in this campaign's
  -- notes, run as a mutation, not committed).
  ------------------------------------------------------------------------

  module Assemble where

    -- the coinduction principle at this relation
    module FR = FSimFromRel Rel fwdE fwdT stabR ndivL

    -- *** THE HEADLINE ***  the CSP-refinement liveness statement, against the
    -- τ-free abstraction.  `LivenessProof` transports it to `breakableSystemOf blkA`
    -- along `sysBisim` (`cong-∖`, `drbisim-sym`, `drbisim→⊑FD`, `⊑FD-trans`) and
    -- closes `∀ b`.  Read it WITH the header's premise audit — the statement is
    -- unconditional in FORM and, since the cellCp3 window, *** UNCONDITIONAL IN FACT
    -- TOO ***: `Sim`'s THREE remaining parameters are (P2)/(P3), supplied as
    -- applications of the CARRIED join, and (P4) `noDivH`, which `LivenessProof`
    -- discharges by name from `LiveHeavyFacts`.  (SUPERSEDED IN PLACE: this read
    -- "premised in FACT at exactly the FOUR parameters of `Sim`: (P1)-(P3), plus (P4)
    -- `noDivH`, which `LivenessProof` discharges by name … and therefore does not ask
    -- of its caller"; (P1) `cellCp3` is a theorem and the parameter is gone.)
    -- (P5) `noRetA`, (P6) `brkBits`, (P7) `prodLands` and (P8) `recvLands` are NOT
    -- premised anywhere any more: they are THEOREMS of §4 (the inert-freeze
    -- conjunct joined to `LegJointB`, refuting the `ret` at node B's frozen KA
    -- client), §A4 (the widened `PES.break-invert`), §A5 (the ⁺ cone's kept
    -- `SrvLands` plus node A's fired-link pin) and §A6 (the node-D peel's carried
    -- consume-driver step).  *** So NO family reaches `LivenessProof.Premises` at
    -- all: (P1) `cellCp3` was the last, and the cellCp3 window discharged it too, so
    -- ALL EIGHT of the original premises are discharged (it read "exactly ONE family
    -- … SEVEN are discharged" until then): (P2)/(P3)'s twelve `InFlightOpen` facts are BUILT there off the
    -- carried join (all nine charted co-position equations being theorems since T11h),
    -- and (P4)-(P8) as described above. ***  All three of instalment 3's kept-class
    -- successor facts are among the discharged.
    -- (SUPERSEDED IN PLACE, §7's drift site: this read "THREE families reach
    -- `LivenessProof.Premises` … exactly FIVE … discharged, three remaining
    -- (P1, P2, P3)" until T12.  (P2)/(P3) were already built rather than premised
    -- before T12; what T12 removed was the last `Premises` FIELD they consumed.)
    lspec-fd : LSpec blkA true true ⊑FD (abstractSystem ∖ hidden blkA)
    lspec-fd = fsim→⊑FD (FR.rel→fsim rel-init)

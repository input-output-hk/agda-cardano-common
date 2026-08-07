{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the per-leg SINGLE-TOKEN pipeline phase-coupling
-- invariant `PipeInv` (`Praos.PipeInv`).
--
-- The block `blkA` flows along a leg (AB→BD for `legBD`, AC→CD for `legCD`)
-- through the chain  prod-Al → cell-l → relay(nodeB/C) → cell-lD → cons-lD.
-- `PipeInv l s` is the MONOTONE TOKEN-PROGRESS invariant that couples the
-- three READABLE driver components of that chain — the producer phase
-- `prod-Al` (a `ProdPh`), the relay phase `cp-B`/`cp-C` (a `CPPh`), and the
-- D-consumer phase `cons-lD` (a `ConsPh`, read via `WalkPr.phOf`) — so that
-- "downstream ≤ upstream" is automatic:
--
--   `PipeInv l s = Σ[ lvl ∈ PLvl ] AtLvl l lvl s`,
--
-- a disjunction over FIVE token positions `L0 … L4` (the block's progress
-- along the chain), each `AtLvl` a conjunction of per-component phase
-- constraints determined by the token:
--
--   L0  prod NOT-sent   · relay PRE      · cons pending   [block at producer]
--   L1  prod sent       · relay PRE      · cons pending   [block in cell-l  ]
--   L2  prod sent       · relay HAS      · cons pending   [block at relay   ]
--   L3  prod sent       · relay FORWARDED· cons pending   [block in cell-lD ]
--   L4  prod sent       · relay FORWARDED· cons RECEIVED  [block delivered  ]
--
-- KEY CONSEQUENCE (this is what `pcone` needs, half (b)):  if `prod-Al ≡ pp5`
-- (the producer is still OFFERING `sendBFBlock`, i.e. NOT-sent) then the token
-- can only be at `L0` (all later levels require the producer to have sent), so
-- the D-consumer is pending (`InCp03`).  A pure, cheap case split
-- (`pipeInv⇒pending` / `pipeInv⇒Pr`).
--
-- BASE:  `pipeInv-init` — at `initial` every component is at its head, so the
-- token sits at `L0`.
--
-- INDEPENDENCE (the leverage):  `PipeInv l s` reads ONLY the three per-leg
-- driver phases, so any transition that leaves those three phases fixed — the
-- OTHER leg, the 8 inert KA/TS/LN/LF peers, the break budget, the other-leg
-- medium cells — preserves `PipeInv l` by the pure frame lemma
-- `pipeInv-frame` (a component-wise `subst`).  This isolates the real work to
-- the leg-`l` component step-cases.
--
-- LIGHT (imports only the state-carrier modules `SysDecode`/`SysNode` +
-- `WalkPr`/`SysReach` accessors; NO SysStep/SysOracle/SysBisim cone).  No
-- postulate/hole/meta.  The medium-cell / peer-FSM strengthening needed to
-- make the leg-`l` step-cases INDUCTIVE (a `PipeInv⁺` refinement), and the
-- preservation proof over `Reachable` (which decodes each transition through
-- the R2 reflection cone), are the multi-session remainder.
------------------------------------------------------------------------

open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( _×_; _,_; Σ; Σ-syntax; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( Block₃; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Base using ( hi; N2N_BlockFetch )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Data p
  using ( Messages; blockFetch; MsgBlock )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; nA; nB; nC; nD; med; initial )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; toSys )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( CopyPhase; empty; full; draining; MedState; phase )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA as SN
open SN
  using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; CPPh; consuming; producing
        ; BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
        ; prod-AB; prod-AC; cp-B; cp-C )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs; legBD; legCD; phOf; InCp03; Pr )

------------------------------------------------------------------------
-- Per-leg READABLE driver-phase accessors: the producer `prod-Al`, the relay
-- `cp-B`/`cp-C`, and (reusing `WalkPr.phOf`) the D-consumer `cons-lD`.
------------------------------------------------------------------------

-- the producer phase on the leg (nodeA's `prod-AB`/`prod-AC`)
prodOf : TwoLegs → SysState → ProdPh
prodOf legBD s = prod-AB (nA s)
prodOf legCD s = prod-AC (nA s)

-- the relay phase on the leg (nodeB's `cp-B` for BD, nodeC's `cp-C` for CD)
relayOf : TwoLegs → SysState → CPPh
relayOf legBD s = cp-B (nB s)
relayOf legCD s = cp-C (nC s)

------------------------------------------------------------------------
-- Per-component progress classifiers (total maps to `Set`).
------------------------------------------------------------------------

-- the producer has SENT the BF block (fired `apiBF sendBFBlock`, `pp5 → pp6`)
ProdSent : ProdPh → Set
ProdSent pp0 = ⊥
ProdSent pp1 = ⊥
ProdSent pp2 = ⊥
ProdSent pp3 = ⊥
ProdSent pp4 = ⊥
ProdSent pp5 = ⊥
ProdSent pp6 = ⊤
ProdSent pp7 = ⊤
ProdSent pp8 = ⊤
ProdSent pp9 = ⊤

-- the producer has NOT yet sent the BF block (`pp0 … pp5`, still offering it)
ProdNotSent : ProdPh → Set
ProdNotSent pp0 = ⊤
ProdNotSent pp1 = ⊤
ProdNotSent pp2 = ⊤
ProdNotSent pp3 = ⊤
ProdNotSent pp4 = ⊤
ProdNotSent pp5 = ⊤
ProdNotSent pp6 = ⊥
ProdNotSent pp7 = ⊥
ProdNotSent pp8 = ⊥
ProdNotSent pp9 = ⊥

-- the relay has NOT yet received the block (consuming, pre-`recvBFBlock` cp0..cp3)
RelayPre : CPPh → Set
RelayPre (consuming _ cp0) = ⊤
RelayPre (consuming _ cp1) = ⊤
RelayPre (consuming _ cp2) = ⊤
RelayPre (consuming _ cp3) = ⊤
RelayPre (consuming _ cp4) = ⊥
RelayPre (consuming _ cp5) = ⊥
RelayPre (consuming _ cp6) = ⊥
RelayPre (producing _ _)   = ⊥

-- the relay HAS the block but has NOT yet forwarded it (finishing the consume
-- tail cp4..cp6, or producing onward pre-`sendBFBlock` pp0..pp5)
RelayHas : CPPh → Set
RelayHas (consuming _ cp0) = ⊥
RelayHas (consuming _ cp1) = ⊥
RelayHas (consuming _ cp2) = ⊥
RelayHas (consuming _ cp3) = ⊥
RelayHas (consuming _ cp4) = ⊤
RelayHas (consuming _ cp5) = ⊤
RelayHas (consuming _ cp6) = ⊤
RelayHas (producing _ pp0) = ⊤
RelayHas (producing _ pp1) = ⊤
RelayHas (producing _ pp2) = ⊤
RelayHas (producing _ pp3) = ⊤
RelayHas (producing _ pp4) = ⊤
RelayHas (producing _ pp5) = ⊤
RelayHas (producing _ pp6) = ⊥
RelayHas (producing _ pp7) = ⊥
RelayHas (producing _ pp8) = ⊥
RelayHas (producing _ pp9) = ⊥

-- the relay has FORWARDED the block onward (producing, past `sendBFBlock` pp6..pp9)
RelayFwd : CPPh → Set
RelayFwd (consuming _ _)   = ⊥
RelayFwd (producing _ pp0) = ⊥
RelayFwd (producing _ pp1) = ⊥
RelayFwd (producing _ pp2) = ⊥
RelayFwd (producing _ pp3) = ⊥
RelayFwd (producing _ pp4) = ⊥
RelayFwd (producing _ pp5) = ⊥
RelayFwd (producing _ pp6) = ⊤
RelayFwd (producing _ pp7) = ⊤
RelayFwd (producing _ pp8) = ⊤
RelayFwd (producing _ pp9) = ⊤

-- the D-consumer has RECEIVED the block (`cp4 … cp6`, post-`recvBFBlock`)
ConsRecv : ConsPh → Set
ConsRecv cp0 = ⊥
ConsRecv cp1 = ⊥
ConsRecv cp2 = ⊥
ConsRecv cp3 = ⊥
ConsRecv cp4 = ⊤
ConsRecv cp5 = ⊤
ConsRecv cp6 = ⊤

------------------------------------------------------------------------
-- The token positions and the per-token per-component phase constraints.
-- Factoring `AtLvl` through the three token→predicate maps `prodP`/`relayP`/
-- `consP` makes the frame lemma a single generic `subst` (no per-level case).
------------------------------------------------------------------------

-- the single-token progress position along the leg pipeline
data PLvl : Set where
  L0 L1 L2 L3 L4 : PLvl

-- the producer constraint at each token position
prodP : PLvl → ProdPh → Set
prodP L0 = ProdNotSent
prodP L1 = ProdSent
prodP L2 = ProdSent
prodP L3 = ProdSent
prodP L4 = ProdSent

-- the relay constraint at each token position
relayP : PLvl → CPPh → Set
relayP L0 = RelayPre
relayP L1 = RelayPre
relayP L2 = RelayHas
relayP L3 = RelayFwd
relayP L4 = RelayFwd

-- the D-consumer constraint at each token position (`InCp03` = pending)
consP : PLvl → ConsPh → Set
consP L0 = InCp03
consP L1 = InCp03
consP L2 = InCp03
consP L3 = InCp03
consP L4 = ConsRecv

-- the token-`lvl` phase constraint on leg `l` at state `s`
AtLvl : TwoLegs → PLvl → SysState → Set
AtLvl l lvl s =
  prodP lvl (prodOf l s) × relayP lvl (relayOf l s) × consP lvl (phOf l s)

-- the per-leg single-token pipeline invariant: the block sits at SOME token
-- position whose per-component constraints hold
PipeInv : TwoLegs → SysState → Set
PipeInv l s = Σ[ lvl ∈ PLvl ] AtLvl l lvl s

------------------------------------------------------------------------
-- BASE CASE — at `initial` the token is at `L0` (producer unstepped `pp0`,
-- relay at its consume head `consuming blkA cp0`, consumer pending `cp0`).
------------------------------------------------------------------------

-- `PipeInv` holds at the initial state for either leg (token at `L0`)
pipeInv-init : (l : TwoLegs) → PipeInv l initial
pipeInv-init legBD = L0 , tt , tt , tt
pipeInv-init legCD = L0 , tt , tt , tt

------------------------------------------------------------------------
-- INDEPENDENCE (frame) — `PipeInv l` depends only on the three leg-`l` driver
-- phases, so a transition that leaves them fixed preserves it component-wise.
-- This is the leverage that discharges the OTHER-leg / inert-peer / break /
-- other-leg-cell transition classes generically once the reflection cone
-- supplies the three phase equalities.
------------------------------------------------------------------------

-- frame preservation: equal leg-`l` driver phases carry `PipeInv l` across
pipeInv-frame : (l : TwoLegs) (s s′ : SysState)
              → prodOf  l s ≡ prodOf  l s′
              → relayOf l s ≡ relayOf l s′
              → phOf    l s ≡ phOf    l s′
              → PipeInv l s → PipeInv l s′
pipeInv-frame l s s′ pe re ce (lvl , hp , hr , hc) =
  lvl , subst (prodP lvl) pe hp , subst (relayP lvl) re hr , subst (consP lvl) ce hc

------------------------------------------------------------------------
-- KEY CONSEQUENCE — the producer still offering `sendBFBlock` (`prod-Al ≡ pp5`,
-- hence NOT-sent) forces the token to `L0`, so the D-consumer is pending.
-- This is `pcone`'s half (b): a pure case split on the token position.
------------------------------------------------------------------------

-- `prod-Al ≡ pp5` ⇒ the D-consumer leg is pre-`recvBFBlock` (`InCp03`)
pipeInv⇒pending : (l : TwoLegs) (s : SysState)
                → prodOf l s ≡ pp5 → PipeInv l s → InCp03 (phOf l s)
pipeInv⇒pending l s eq (L0 , _ , _ , hc) = hc
pipeInv⇒pending l s eq (L1 , _ , _ , hc) = hc
pipeInv⇒pending l s eq (L2 , _ , _ , hc) = hc
pipeInv⇒pending l s eq (L3 , _ , _ , hc) = hc
-- L4 forces the producer to have SENT; `prod-Al ≡ pp5` (not-sent) refutes it
pipeInv⇒pending l s eq (L4 , hp , _ , _) = ⊥-elim (subst ProdSent eq hp)

-- packaged at the reachable-config level: `PipeInv` + `prod-Al ≡ pp5` yields
-- the leg-tagged pending witness `Pr b r` that `pcone` must return
pipeInv⇒Pr : (b : Block₃) (l : TwoLegs) (r : RState)
           → prodOf l (toSys r) ≡ pp5 → PipeInv l (toSys r) → Pr b r
pipeInv⇒Pr b l r eq pinv = l , pipeInv⇒pending l (toSys r) eq pinv

------------------------------------------------------------------------
-- Component progress-class exclusivity (the level-elimination helpers used by
-- the boundary-crossing step-cases below).
------------------------------------------------------------------------

-- a producer phase cannot be both sent and not-sent
prodSent-notSent-⊥ : (p : ProdPh) → ProdSent p → ProdNotSent p → ⊥
prodSent-notSent-⊥ pp0 () _
prodSent-notSent-⊥ pp1 () _
prodSent-notSent-⊥ pp2 () _
prodSent-notSent-⊥ pp3 () _
prodSent-notSent-⊥ pp4 () _
prodSent-notSent-⊥ pp5 () _
prodSent-notSent-⊥ pp6 _ ()
prodSent-notSent-⊥ pp7 _ ()
prodSent-notSent-⊥ pp8 _ ()
prodSent-notSent-⊥ pp9 _ ()

-- a relay phase cannot be both pre-receive and holding
relayPre-has-⊥ : (r : CPPh) → RelayPre r → RelayHas r → ⊥
relayPre-has-⊥ (consuming _ cp0) _ ()
relayPre-has-⊥ (consuming _ cp1) _ ()
relayPre-has-⊥ (consuming _ cp2) _ ()
relayPre-has-⊥ (consuming _ cp3) _ ()
relayPre-has-⊥ (consuming _ cp4) () _
relayPre-has-⊥ (consuming _ cp5) () _
relayPre-has-⊥ (consuming _ cp6) () _
relayPre-has-⊥ (producing _ _)   () _

-- a relay phase cannot be both forwarded and merely holding
relayFwd-has-⊥ : (r : CPPh) → RelayFwd r → RelayHas r → ⊥
relayFwd-has-⊥ (consuming _ _)   () _
relayFwd-has-⊥ (producing _ pp0) () _
relayFwd-has-⊥ (producing _ pp1) () _
relayFwd-has-⊥ (producing _ pp2) () _
relayFwd-has-⊥ (producing _ pp3) () _
relayFwd-has-⊥ (producing _ pp4) () _
relayFwd-has-⊥ (producing _ pp5) () _
relayFwd-has-⊥ (producing _ pp6) _ ()
relayFwd-has-⊥ (producing _ pp7) _ ()
relayFwd-has-⊥ (producing _ pp8) _ ()
relayFwd-has-⊥ (producing _ pp9) _ ()

------------------------------------------------------------------------
-- LEG-`l` COMPONENT STEP-CASE CORES (pure phase logic; NO oracle).  Each takes
-- the "one driver moved, the other two fixed" facts the R2 reflection cone will
-- later supply for a concrete leg-`l` transition, and advances/preserves the
-- token.  These discharge the SAME-block-holder monotone transitions of every
-- component.  The TWO receive-boundary crossings (relay `recvBFBlock` `L1→L2`,
-- consumer `recvBFBlock` `L3→L4`) are NOT spine-provable and need the
-- cell-coupling strengthening (see the module header / report) — they are the
-- deliberately-omitted step-cases.
------------------------------------------------------------------------

-- PRODUCER internal step (stays within its sent/not-sent class): relay + cons
-- fixed.  Covers every `prod-Al` api hop that does NOT fire `sendBFBlock`.
pipeInv-prod-move : (l : TwoLegs) (s s′ : SysState)
  → relayOf l s ≡ relayOf l s′ → phOf l s ≡ phOf l s′
  → (ProdNotSent (prodOf l s) → ProdNotSent (prodOf l s′))
  → (ProdSent    (prodOf l s) → ProdSent    (prodOf l s′))
  → PipeInv l s → PipeInv l s′
pipeInv-prod-move l s s′ re ce fN fS (L0 , hp , hr , hc) = L0 , fN hp , subst RelayPre re hr , subst InCp03 ce hc
pipeInv-prod-move l s s′ re ce fN fS (L1 , hp , hr , hc) = L1 , fS hp , subst RelayPre re hr , subst InCp03 ce hc
pipeInv-prod-move l s s′ re ce fN fS (L2 , hp , hr , hc) = L2 , fS hp , subst RelayHas re hr , subst InCp03 ce hc
pipeInv-prod-move l s s′ re ce fN fS (L3 , hp , hr , hc) = L3 , fS hp , subst RelayFwd re hr , subst InCp03 ce hc
pipeInv-prod-move l s s′ re ce fN fS (L4 , hp , hr , hc) = L4 , fS hp , subst RelayFwd re hr , subst ConsRecv ce hc

-- PRODUCER send step (`sendBFBlock`, `pp5 → pp6`, not-sent → sent, `L0 → L1`):
-- relay + cons fixed.  This is the first hand-off; needs no upstream coupling.
pipeInv-prod-send : (l : TwoLegs) (s s′ : SysState)
  → relayOf l s ≡ relayOf l s′ → phOf l s ≡ phOf l s′
  → ProdNotSent (prodOf l s) → ProdSent (prodOf l s′)
  → PipeInv l s → PipeInv l s′
pipeInv-prod-send l s s′ re ce nN sS (L0 , hp , hr , hc) = L1 , sS , subst RelayPre re hr , subst InCp03 ce hc
pipeInv-prod-send l s s′ re ce nN sS (L1 , hp , hr , hc) = ⊥-elim (prodSent-notSent-⊥ _ hp nN)
pipeInv-prod-send l s s′ re ce nN sS (L2 , hp , hr , hc) = ⊥-elim (prodSent-notSent-⊥ _ hp nN)
pipeInv-prod-send l s s′ re ce nN sS (L3 , hp , hr , hc) = ⊥-elim (prodSent-notSent-⊥ _ hp nN)
pipeInv-prod-send l s s′ re ce nN sS (L4 , hp , hr , hc) = ⊥-elim (prodSent-notSent-⊥ _ hp nN)

-- RELAY internal step (stays within its pre/has/fwd class): prod + cons fixed.
-- Covers every relay hop that does NOT cross a receive/forward boundary
-- (consume-tail advances, produce-tail advances).
pipeInv-relay-move : (l : TwoLegs) (s s′ : SysState)
  → prodOf l s ≡ prodOf l s′ → phOf l s ≡ phOf l s′
  → (RelayPre (relayOf l s) → RelayPre (relayOf l s′))
  → (RelayHas (relayOf l s) → RelayHas (relayOf l s′))
  → (RelayFwd (relayOf l s) → RelayFwd (relayOf l s′))
  → PipeInv l s → PipeInv l s′
pipeInv-relay-move l s s′ pe ce fP fH fF (L0 , hp , hr , hc) = L0 , subst ProdNotSent pe hp , fP hr , subst InCp03 ce hc
pipeInv-relay-move l s s′ pe ce fP fH fF (L1 , hp , hr , hc) = L1 , subst ProdSent pe hp , fP hr , subst InCp03 ce hc
pipeInv-relay-move l s s′ pe ce fP fH fF (L2 , hp , hr , hc) = L2 , subst ProdSent pe hp , fH hr , subst InCp03 ce hc
pipeInv-relay-move l s s′ pe ce fP fH fF (L3 , hp , hr , hc) = L3 , subst ProdSent pe hp , fF hr , subst InCp03 ce hc
pipeInv-relay-move l s s′ pe ce fP fH fF (L4 , hp , hr , hc) = L4 , subst ProdSent pe hp , fF hr , subst ConsRecv ce hc

-- RELAY forward step (`sendBFBlock` on the onward link, holding → forwarded,
-- `L2 → L3`): prod + cons fixed.  Spine-provable — at `L2` the producer is
-- already sent, so no cell coupling is needed for the level increment.
pipeInv-relay-fwd : (l : TwoLegs) (s s′ : SysState)
  → prodOf l s ≡ prodOf l s′ → phOf l s ≡ phOf l s′
  → RelayHas (relayOf l s) → RelayFwd (relayOf l s′)
  → PipeInv l s → PipeInv l s′
pipeInv-relay-fwd l s s′ pe ce hHas hFwd (L2 , hp , hr , hc) = L3 , subst ProdSent pe hp , hFwd , subst InCp03 ce hc
pipeInv-relay-fwd l s s′ pe ce hHas hFwd (L0 , hp , hr , hc) = ⊥-elim (relayPre-has-⊥ _ hr hHas)
pipeInv-relay-fwd l s s′ pe ce hHas hFwd (L1 , hp , hr , hc) = ⊥-elim (relayPre-has-⊥ _ hr hHas)
pipeInv-relay-fwd l s s′ pe ce hHas hFwd (L3 , hp , hr , hc) = ⊥-elim (relayFwd-has-⊥ _ hr hHas)
pipeInv-relay-fwd l s s′ pe ce hHas hFwd (L4 , hp , hr , hc) = ⊥-elim (relayFwd-has-⊥ _ hr hHas)

-- CONSUMER internal step (stays within its pending/received class): prod +
-- relay fixed.  Covers the pending advances (`cp0..cp3`, e.g. `recvCSRollforward`,
-- `sendBFRequestRange`) and the received-tail advances (`cp4..cp6`).
pipeInv-cons-move : (l : TwoLegs) (s s′ : SysState)
  → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
  → (InCp03   (phOf l s) → InCp03   (phOf l s′))
  → (ConsRecv (phOf l s) → ConsRecv (phOf l s′))
  → PipeInv l s → PipeInv l s′
pipeInv-cons-move l s s′ pe re fI fR (L0 , hp , hr , hc) = L0 , subst ProdNotSent pe hp , subst RelayPre re hr , fI hc
pipeInv-cons-move l s s′ pe re fI fR (L1 , hp , hr , hc) = L1 , subst ProdSent pe hp , subst RelayPre re hr , fI hc
pipeInv-cons-move l s s′ pe re fI fR (L2 , hp , hr , hc) = L2 , subst ProdSent pe hp , subst RelayHas re hr , fI hc
pipeInv-cons-move l s s′ pe re fI fR (L3 , hp , hr , hc) = L3 , subst ProdSent pe hp , subst RelayFwd re hr , fI hc
pipeInv-cons-move l s s′ pe re fI fR (L4 , hp , hr , hc) = L4 , subst ProdSent pe hp , subst RelayFwd re hr , fR hc

------------------------------------------------------------------------
-- STRENGTHENING `PipeInv⁺` — the medium-cell + BF-client-peer coupling that
-- makes the TWO receive-boundary crossings INDUCTIVE.
--
-- ENCODING FINDING (session 1) reprise: the 3-driver spine `PipeInv` is a SOUND
-- statement but NOT self-inductive at the two `recvBFBlock` crossings, because
-- the breaking config `(prod NotSent, relay Pre, cons cp3, cell-lD full)` is
-- spine-admitted at `L0`.  The receive of a block is an `apiBF … recvBFBlock`
-- handshake between the leg's DRIVER and its LOCAL BlockFetch CLIENT peer — and
-- that client peer only offers `recvBFBlock` once it holds the block (`bcBlk1`),
-- which it obtained from the medium cell (an io `output`) which in turn was
-- filled by the upstream sender.  So the coupling that gates a receive is
-- "the leg's BF CLIENT peer holds a block ⇒ its upstream has already forwarded",
-- and (for the io hand-offs that PART-1 preservation must chain) the mirror
-- "the leg's medium cell is non-empty ⇒ its upstream has already forwarded".
--
-- `PipeInv⁺ l s = PipeInv l s × Coupled l s`, with `Coupled` the four
-- implications (upstream cell / upstream client ⇒ `ProdSent`; downstream cell /
-- downstream client ⇒ `RelayFwd`).  This EXCLUDES the breaking config
-- (its `cell-lD full` with `relay Pre` violates the downstream-cell clause) and
-- supplies the receive cores exactly the `ProdSent`/`RelayFwd` fact they need to
-- pin the token to `L1`/`L3` before the increment.  `PipeInv⁺ ⇒ PipeInv` is
-- `proj₁`, so the `pcone` consequence still flows.  Still LIGHT (pure phase
-- logic on readable driver / cell / peer components; no oracle).
------------------------------------------------------------------------

-- the leg's UPSTREAM medium cell (`cell-l`: the block's first hop A→relay) —
-- the BlockFetch `(hi)` copy cell on link AB (`legBD`) / AC (`legCD`)
cellUp : TwoLegs → SysState → CopyPhase
cellUp legBD s = phase (med s) linkAB hi N2N_BlockFetch
cellUp legCD s = phase (med s) linkAC hi N2N_BlockFetch

-- the leg's DOWNSTREAM medium cell (`cell-lD`: the block's second hop relay→D) —
-- the BlockFetch `(hi)` copy cell on link BD (`legBD`) / CD (`legCD`)
cellDn : TwoLegs → SysState → CopyPhase
cellDn legBD s = phase (med s) linkBD hi N2N_BlockFetch
cellDn legCD s = phase (med s) linkCD hi N2N_BlockFetch

-- the leg's UPSTREAM BF CLIENT peer (the relay's client reading `cell-l`):
-- nodeB's client on link AB (`legBD`) / nodeC's client on link AC (`legCD`)
upClient : TwoLegs → SysState → BFcPos
upClient legBD s = SN.NodeStateB.bfC-AB (nB s)
upClient legCD s = SN.NodeStateC.bfC-AC (nC s)

-- the leg's DOWNSTREAM BF CLIENT peer (nodeD's client reading `cell-lD`):
-- nodeD's client on link BD (`legBD`) / on link CD (`legCD`)
dnClient : TwoLegs → SysState → BFcPos
dnClient legBD s = SN.NodeStateD.bfC-BD (nD s)
dnClient legCD s = SN.NodeStateD.bfC-CD (nD s)

-- a BlockFetch wire message that CARRIES A BLOCK (`MsgBlock`); every other
-- message on the same channel (`MsgStartBatch`/`MsgNoBlocks`/`MsgBatchDone`/
-- `MsgRequestRange`/`MsgClientDone`) and every non-BF message is not one
MsgIsBlk : Messages → Set
MsgIsBlk (blockFetch (MsgBlock _)) = ⊤
MsgIsBlk _                         = ⊥

-- a medium copy cell HOLDS A FETCHED BLOCK (`full`/`draining` whose payload is
-- a BlockFetch `MsgBlock`).
--
-- SESSION-28 CORRECTION (see `Praos.PipeCellFalse`, a machine-checked
-- refutation).  This used to be mere NON-EMPTINESS (`CellNE`), which made
-- `Coupled`'s two cell clauses FALSE: a copy cell is keyed only by
-- `(link, dir, IDs)`, so ALL BlockFetch messages on the leg share ONE cell, and
-- node A's BF server writes `MsgStartBatch` into `cellUp` while the producer
-- driver is still at `pp5` (`ProdSent pp5 = ⊥`).  Worse, the server offers no
-- api `sendBFBlock` until that wire-send has fired, so the violating state lies
-- on EVERY block-delivering run.  Refining the antecedent to "holds a
-- `MsgBlock`" restores the truth of the clauses without weakening what the
-- receive-boundary cores consume: a BF client enters `bcBlk1` only by reading a
-- `MsgBlock`, so the drain hand-off still gets its `ProdSent`/`RelayFwd`.
CellHasBlk : CopyPhase → Set
CellHasBlk empty                      = ⊥
CellHasBlk (full     (_ , _ , _ , m)) = MsgIsBlk m
CellHasBlk (draining (_ , _ , _ , m)) = MsgIsBlk m

-- a BF client peer HOLDS a block (is in `bcBlk1`, offering `recvBFBlock`)
BFcHasBlk : BFcPos → Set
BFcHasBlk (bcHead _) = ⊥
BFcHasBlk (bcReq1 _) = ⊥
BFcHasBlk bcDone1    = ⊥
BFcHasBlk (bcBlk1 _) = ⊤
BFcHasBlk (bcSil _)  = ⊥

-- the coupling: a non-empty upstream cell / a holding upstream client forces the
-- producer to have SENT; a non-empty downstream cell / a holding downstream
-- client forces the relay to have FORWARDED
Coupled : TwoLegs → SysState → Set
Coupled l s =
    (CellHasBlk     (cellUp   l s) → ProdSent (prodOf l s))
  × (BFcHasBlk  (upClient l s) → ProdSent (prodOf l s))
  × (CellHasBlk     (cellDn   l s) → RelayFwd (relayOf l s))
  × (BFcHasBlk  (dnClient l s) → RelayFwd (relayOf l s))

-- the strengthened per-leg single-token pipeline invariant
PipeInv⁺ : TwoLegs → SysState → Set
PipeInv⁺ l s = PipeInv l s × Coupled l s

-- forget the coupling: `PipeInv⁺` still entails `PipeInv` (so `pipeInv⇒Pr` flows)
pipeInv⁺⇒PipeInv : (l : TwoLegs) (s : SysState) → PipeInv⁺ l s → PipeInv l s
pipeInv⁺⇒PipeInv l s = proj₁

------------------------------------------------------------------------
-- BASE — at `initial` every cell is `empty` and every BF client peer is at its
-- idle loop head, so all four coupling antecedents are uninhabited.
------------------------------------------------------------------------

-- `PipeInv⁺` holds at the initial state for either leg (token `L0`, coupling
-- vacuous: cells `empty`, clients `bcHead`)
pipeInv⁺-init : (l : TwoLegs) → PipeInv⁺ l initial
pipeInv⁺-init legBD = pipeInv-init legBD , (λ ()) , (λ ()) , (λ ()) , (λ ())
pipeInv⁺-init legCD = pipeInv-init legCD , (λ ()) , (λ ()) , (λ ()) , (λ ())

------------------------------------------------------------------------
-- INDEPENDENCE (frame) — a transition fixing ALL seven leg-`l` components (the
-- three drivers, the two cells, the two BF client peers) preserves `PipeInv⁺`.
------------------------------------------------------------------------

-- transport an implication across equalities of its antecedent- and
-- consequent-carrying components
transImp : {A B : Set} (P : A → Set) (Q : B → Set) {a a′ : A} {b b′ : B}
         → a ≡ a′ → b ≡ b′ → (P a → Q b) → (P a′ → Q b′)
transImp P Q ea eb f h = subst Q eb (f (subst P (sym ea) h))

-- frame preservation for `PipeInv⁺` (all seven leg-`l` components fixed)
pipeInv⁺-frame : (l : TwoLegs) (s s′ : SysState)
               → prodOf   l s ≡ prodOf   l s′
               → relayOf  l s ≡ relayOf  l s′
               → phOf     l s ≡ phOf     l s′
               → cellUp   l s ≡ cellUp   l s′
               → cellDn   l s ≡ cellDn   l s′
               → upClient l s ≡ upClient l s′
               → dnClient l s ≡ dnClient l s′
               → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-frame l s s′ pe re ce cue cde ue de (pinv , cu , uc , cd , dc) =
    pipeInv-frame l s s′ pe re ce pinv
  , transImp CellHasBlk    ProdSent cue pe cu
  , transImp BFcHasBlk ProdSent ue  pe uc
  , transImp CellHasBlk    RelayFwd cde re cd
  , transImp BFcHasBlk RelayFwd de  re dc

------------------------------------------------------------------------
-- THE MAXIMAL DRIVER-FIXED PRESERVATION CORE (session 28).
--
-- Every hidden-io hand-off (cell fill / cell output / autonomous drain-to-empty
-- / client advance) keeps the three leg DRIVERS fixed and moves some subset of
-- the four coupling components.  Rather than one core per hand-off shape (the
-- six `PipeIoHandoff` cores, each of which had to guess which io-source fact
-- its caller could supply), this single core takes, PER COUPLING CLAUSE, the
-- MAXIMAL three-arm evolution witness
--
--     component fixed  ⊎  antecedent refuted at s′  ⊎  consequent true at s′
--
-- and discharges the clause from whichever arm the peel can actually produce.
-- It subsumes `pipeInv⁺-frame` and all six `PipeIoHandoff` cores, so no future
-- layer can under-provision it: an arm it never uses costs nothing.
------------------------------------------------------------------------

-- the maximal per-clause evolution witness for ONE `Coupled` clause: the
-- antecedent component is unchanged, or its antecedent is refuted after the
-- step, or the clause's consequent already holds after the step
data ClauseEvo {A : Set} (P : A → Set) (Q : Set) (a a′ : A) : Set where
  cvFix : a ≡ a′        → ClauseEvo P Q a a′   -- component unchanged
  cvNo  : (P a′ → ⊥)    → ClauseEvo P Q a a′   -- antecedent refuted at s′
  cvYes : Q             → ClauseEvo P Q a a′   -- consequent established at s′

-- discharge ONE clause at `s′` from its evolution plus the consequent-monotone
-- map along the (driver-fixed or driver-advancing) step
clause-pres : {A : Set} (P : A → Set) {Q Q′ : Set} {a a′ : A}
            → (Q → Q′) → ClauseEvo P Q′ a a′ → (P a → Q) → (P a′ → Q′)
clause-pres P mono (cvFix eq)  f h = mono (f (subst P (sym eq) h))
clause-pres P mono (cvNo  ¬h)  f h = ⊥-elim (¬h h)
clause-pres P mono (cvYes q)   f h = q

-- DRIVER-FIXED preservation from four per-clause evolutions.  The drivers are
-- fixed, so both consequents transport by `subst`; each coupling clause is then
-- discharged by whichever arm its peel supplies.
pipeInv⁺-io : (l : TwoLegs) (s s′ : SysState)
  → prodOf  l s ≡ prodOf  l s′
  → relayOf l s ≡ relayOf l s′
  → phOf    l s ≡ phOf    l s′
  → ClauseEvo CellHasBlk (ProdSent (prodOf  l s′)) (cellUp   l s) (cellUp   l s′)
  → ClauseEvo BFcHasBlk  (ProdSent (prodOf  l s′)) (upClient l s) (upClient l s′)
  → ClauseEvo CellHasBlk (RelayFwd (relayOf l s′)) (cellDn   l s) (cellDn   l s′)
  → ClauseEvo BFcHasBlk  (RelayFwd (relayOf l s′)) (dnClient l s) (dnClient l s′)
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-io l s s′ pe re ce ecu euc ecd edc (pinv , cu , uc , cd , dc) =
    pipeInv-frame l s s′ pe re ce pinv
  , clause-pres CellHasBlk (subst ProdSent pe) ecu cu
  , clause-pres BFcHasBlk  (subst ProdSent pe) euc uc
  , clause-pres CellHasBlk (subst RelayFwd re) ecd cd
  , clause-pres BFcHasBlk  (subst RelayFwd re) edc dc

------------------------------------------------------------------------
-- Extra progress-class exclusivity helpers for the receive crossings.
------------------------------------------------------------------------

-- a relay phase cannot be both pre-receive and forwarded
relayPre-fwd-⊥ : (r : CPPh) → RelayPre r → RelayFwd r → ⊥
relayPre-fwd-⊥ (consuming _ cp0) _ ()
relayPre-fwd-⊥ (consuming _ cp1) _ ()
relayPre-fwd-⊥ (consuming _ cp2) _ ()
relayPre-fwd-⊥ (consuming _ cp3) _ ()
relayPre-fwd-⊥ (consuming _ cp4) () _
relayPre-fwd-⊥ (consuming _ cp5) () _
relayPre-fwd-⊥ (consuming _ cp6) () _
relayPre-fwd-⊥ (producing _ _)   () _

-- a consumer phase cannot be both pending and received
inCp03-recv-⊥ : (c : ConsPh) → InCp03 c → ConsRecv c → ⊥
inCp03-recv-⊥ cp0 _ ()
inCp03-recv-⊥ cp1 _ ()
inCp03-recv-⊥ cp2 _ ()
inCp03-recv-⊥ cp3 _ ()
inCp03-recv-⊥ cp4 () _
inCp03-recv-⊥ cp5 () _
inCp03-recv-⊥ cp6 () _

------------------------------------------------------------------------
-- THE TWO RECEIVE-BOUNDARY CROSSING CORES (now inductive under `PipeInv⁺`).
------------------------------------------------------------------------

-- RELAY receive (`recvBFBlock` on the upstream link, consuming `cp3 → cp4`,
-- `RelayPre → RelayHas`, `L1 → L2`).  The relay's upstream BF client held a block
-- at `s` (`hUp`), so by the coupling the producer is SENT — which rules out `L0`
-- (the only other pre-receive level); the `RelayPre` premise rules out `L2..L4`.
-- The step touches ONLY the relay driver + the upstream client (prod / cons /
-- cells / downstream client all fixed).
pipeInv⁺-relay-recv : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′
  → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′
  → cellDn   l s ≡ cellDn   l s′
  → dnClient l s ≡ dnClient l s′
  → RelayPre (relayOf l s)              -- pre: relay still consuming (about to receive)
  → BFcHasBlk (upClient l s)            -- pre: the relay's upstream client holds the block
  → RelayHas (relayOf l s′)             -- post: relay now holds the block (`cp4`)
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-relay-recv l s s′ pe ce cue cde de hrPre hUp hHas′ ((lvl , hp , hr , hc) , cu , uc , cd , dc)
  = (L2 , tok lvl hp hr hc) , cell1 , client1 , cell3 , client3
  where
  hSent : ProdSent (prodOf l s)
  hSent = uc hUp
  nfwd : RelayFwd (relayOf l s) → ⊥
  nfwd = relayPre-fwd-⊥ (relayOf l s) hrPre
  -- the token advance: only `L1` survives; produces `L2`
  tok : (lvl : PLvl) → prodP lvl (prodOf l s) → relayP lvl (relayOf l s) → consP lvl (phOf l s)
      → AtLvl l L2 s′
  tok L0 hp hr hc = ⊥-elim (prodSent-notSent-⊥ _ hSent hp)
  tok L1 hp hr hc = subst ProdSent pe hSent , hHas′ , subst InCp03 ce hc
  tok L2 hp hr hc = ⊥-elim (relayPre-has-⊥ _ hrPre hr)
  tok L3 hp hr hc = ⊥-elim (nfwd hr)
  tok L4 hp hr hc = ⊥-elim (nfwd hr)
  cell1   : CellHasBlk (cellUp l s′) → ProdSent (prodOf l s′)
  cell1   = transImp CellHasBlk ProdSent cue pe cu
  client1 : BFcHasBlk (upClient l s′) → ProdSent (prodOf l s′)
  client1 = λ _ → subst ProdSent pe hSent
  cell3   : CellHasBlk (cellDn l s′) → RelayFwd (relayOf l s′)
  cell3   = λ h → ⊥-elim (nfwd (cd (subst CellHasBlk (sym cde) h)))
  client3 : BFcHasBlk (dnClient l s′) → RelayFwd (relayOf l s′)
  client3 = λ h → ⊥-elim (nfwd (dc (subst BFcHasBlk (sym de) h)))

-- CONSUMER receive (`recvBFBlock` on the downstream link, `cp3 → cp4`,
-- `InCp03 → ConsRecv`, `L3 → L4`).  nodeD's downstream BF client held the block
-- at `s` (`hDn`), so the relay is FORWARDED — ruling out `L0..L2`; the `InCp03`
-- premise rules out `L4`.  The step touches ONLY the consumer driver + the
-- downstream client (prod / relay / cells / upstream client all fixed).
pipeInv⁺-cons-recv : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′
  → relayOf  l s ≡ relayOf  l s′
  → cellUp   l s ≡ cellUp   l s′
  → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′
  → InCp03 (phOf l s)                   -- pre: consumer still pending
  → BFcHasBlk (dnClient l s)            -- pre: nodeD's downstream client holds the block
  → ConsRecv (phOf l s′)                -- post: consumer has received (`cp4`)
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-cons-recv l s s′ pe re cue cde ue hPre hDn hRecv′ ((lvl , hp , hr , hc) , cu , uc , cd , dc)
  = (L4 , tok lvl hp hr hc) , cell1 , client1 , cell3 , client3
  where
  hFwd : RelayFwd (relayOf l s)
  hFwd = dc hDn
  -- the token advance: only `L3` survives; produces `L4`
  tok : (lvl : PLvl) → prodP lvl (prodOf l s) → relayP lvl (relayOf l s) → consP lvl (phOf l s)
      → AtLvl l L4 s′
  tok L0 hp hr hc = ⊥-elim (relayPre-fwd-⊥ _ hr hFwd)
  tok L1 hp hr hc = ⊥-elim (relayPre-fwd-⊥ _ hr hFwd)
  tok L2 hp hr hc = ⊥-elim (relayFwd-has-⊥ _ hFwd hr)
  tok L3 hp hr hc = subst ProdSent pe hp , subst RelayFwd re hFwd , hRecv′
  tok L4 hp hr hc = ⊥-elim (inCp03-recv-⊥ _ hPre hc)
  cell1   : CellHasBlk (cellUp l s′) → ProdSent (prodOf l s′)
  cell1   = transImp CellHasBlk ProdSent cue pe cu
  client1 : BFcHasBlk (upClient l s′) → ProdSent (prodOf l s′)
  client1 = transImp BFcHasBlk ProdSent ue pe uc
  cell3   : CellHasBlk (cellDn l s′) → RelayFwd (relayOf l s′)
  cell3   = transImp CellHasBlk RelayFwd cde re cd
  client3 : BFcHasBlk (dnClient l s′) → RelayFwd (relayOf l s′)
  client3 = λ _ → subst RelayFwd re hFwd

------------------------------------------------------------------------
-- THE FIVE `PipeInv⁺` (coupling-carrying) MOVE CORES.
--
-- The plain move cores above preserve `PipeInv`, but the STRENGTHENED
-- invariant `PipeInv⁺ = PipeInv × Coupled` also needs `Coupled l s′` carried
-- across.  Each of these five wraps its plain core and additionally transports
-- the four coupling implications, given the leg-`l` cell/client component
-- deltas the (non-driver) components hold across the step.  Together with the
-- two receive cores above and `pipeInv⁺-frame`, this is EVERY leg-`l` advance
-- as a `PipeInv⁺`-preserving core — the complete phase-logic side of
-- preservation (nothing here touches the oracle; pure phase logic on the seven
-- readable components).
------------------------------------------------------------------------

-- PRODUCER internal step (⁺): prod monotone within its class; relay + cons +
-- both cells + both clients fixed.  The upstream coupling consequents move with
-- the producer (`fS`); the downstream ones are relay-fixed (`transImp`).
pipeInv⁺-prod-move : (l : TwoLegs) (s s′ : SysState)
  → relayOf  l s ≡ relayOf  l s′ → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
  → (ProdNotSent (prodOf l s) → ProdNotSent (prodOf l s′))
  → (ProdSent    (prodOf l s) → ProdSent    (prodOf l s′))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-prod-move l s s′ re ce cue cde ue de fN fS (pinv , cu , uc , cd , dc)
  = pipeInv-prod-move l s s′ re ce fN fS pinv
  , (λ h → fS (cu (subst CellHasBlk    (sym cue) h)))
  , (λ h → fS (uc (subst BFcHasBlk (sym ue)  h)))
  , transImp CellHasBlk    RelayFwd cde re cd
  , transImp BFcHasBlk RelayFwd de  re dc

-- PRODUCER send step (⁺, `L0 → L1`): relay + cons + downstream cell/client
-- fixed.  The producer is now SENT (`sS`), so the two upstream coupling clauses
-- hold outright; the downstream two are relay-fixed.
pipeInv⁺-prod-send : (l : TwoLegs) (s s′ : SysState)
  → relayOf  l s ≡ relayOf  l s′ → phOf     l s ≡ phOf     l s′
  → cellDn   l s ≡ cellDn   l s′ → dnClient l s ≡ dnClient l s′
  → ProdNotSent (prodOf l s) → ProdSent (prodOf l s′)
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-prod-send l s s′ re ce cde de nN sS (pinv , cu , uc , cd , dc)
  = pipeInv-prod-send l s s′ re ce nN sS pinv
  , (λ _ → sS) , (λ _ → sS)
  , transImp CellHasBlk    RelayFwd cde re cd
  , transImp BFcHasBlk RelayFwd de  re dc

-- RELAY internal step (⁺): relay monotone within its class; prod + cons + both
-- cells + both clients fixed.  Upstream coupling is prod-fixed; the downstream
-- consequents move with the relay (`fF`).
pipeInv⁺-relay-move : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′ → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
  → (RelayPre (relayOf l s) → RelayPre (relayOf l s′))
  → (RelayHas (relayOf l s) → RelayHas (relayOf l s′))
  → (RelayFwd (relayOf l s) → RelayFwd (relayOf l s′))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-relay-move l s s′ pe ce cue cde ue de fP fH fF (pinv , cu , uc , cd , dc)
  = pipeInv-relay-move l s s′ pe ce fP fH fF pinv
  , transImp CellHasBlk    ProdSent cue pe cu
  , transImp BFcHasBlk ProdSent ue  pe uc
  , (λ h → fF (cd (subst CellHasBlk    (sym cde) h)))
  , (λ h → fF (dc (subst BFcHasBlk (sym de)  h)))

-- RELAY forward step (⁺, `L2 → L3`): prod + cons + upstream cell/client fixed.
-- The relay is now FORWARDED (`hFwd`), so the two downstream coupling clauses
-- hold outright; the upstream two are prod-fixed.
pipeInv⁺-relay-fwd : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′ → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → upClient l s ≡ upClient l s′
  → RelayHas (relayOf l s) → RelayFwd (relayOf l s′)
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-relay-fwd l s s′ pe ce cue ue hHas hFwd (pinv , cu , uc , cd , dc)
  = pipeInv-relay-fwd l s s′ pe ce hHas hFwd pinv
  , transImp CellHasBlk    ProdSent cue pe cu
  , transImp BFcHasBlk ProdSent ue  pe uc
  , (λ _ → hFwd) , (λ _ → hFwd)

-- CONSUMER internal step (⁺): cons monotone within its class; prod + relay +
-- both cells + both clients fixed.  The consumer does not appear in `Coupled`,
-- so all four clauses transport by `transImp` on the fixed prod/relay drivers.
pipeInv⁺-cons-move : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
  → (InCp03   (phOf l s) → InCp03   (phOf l s′))
  → (ConsRecv (phOf l s) → ConsRecv (phOf l s′))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-cons-move l s s′ pe re cue cde ue de fI fR (pinv , cu , uc , cd , dc)
  = pipeInv-cons-move l s s′ pe re fI fR pinv
  , transImp CellHasBlk    ProdSent cue pe cu
  , transImp BFcHasBlk ProdSent ue  pe uc
  , transImp CellHasBlk    RelayFwd cde re cd
  , transImp BFcHasBlk RelayFwd de  re dc

------------------------------------------------------------------------
-- THE STEP-CLASS ENUM `PipeStep⁺` + the TOTAL dispatcher `pipeInv⁺-step`.
--
-- `PipeStep⁺ l s s′` names WHICH leg-`l` transition class carried `s` to `s′`,
-- packaging exactly the per-component delta each core consumes.  `pipeInv⁺-step`
-- dispatches to the matching core, so `PipeInv⁺` is preserved across ANY step
-- once it is classified.  This is the CONSUMER-SIDE decode-bridge interface:
-- the remaining (oracle-scale) work is to PRODUCE a `PipeStep⁺` from a reflected
-- forward step — i.e. an "expose" cone à la `WalkDExpose.DReport` extended to
-- all seven leg-`l` components (see the report's re-framing).  The dispatcher
-- itself is pure phase logic (no oracle), and it is TOTAL: every leg-`l` advance
-- is covered (frame, two producer, two relay, one relay-receive, one consumer,
-- one consumer-receive).
------------------------------------------------------------------------

-- the classification of one leg-`l` transition `s ↝ s′` into a token-progress
-- class carrying its per-component deltas (the eight preservation cores)
data PipeStep⁺ (l : TwoLegs) (s s′ : SysState) : Set where
  -- all seven leg-`l` components fixed (other leg / inert peer / break / …)
  psFrame : prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
          → phOf l s ≡ phOf l s′ → cellUp l s ≡ cellUp l s′
          → cellDn l s ≡ cellDn l s′ → upClient l s ≡ upClient l s′
          → dnClient l s ≡ dnClient l s′ → PipeStep⁺ l s s′
  -- producer internal hop (class-preserving)
  psProdMove : relayOf l s ≡ relayOf l s′ → phOf l s ≡ phOf l s′
             → cellUp l s ≡ cellUp l s′ → cellDn l s ≡ cellDn l s′
             → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
             → (ProdNotSent (prodOf l s) → ProdNotSent (prodOf l s′))
             → (ProdSent (prodOf l s) → ProdSent (prodOf l s′))
             → PipeStep⁺ l s s′
  -- producer send (`sendBFBlock`, `L0 → L1`)
  psProdSend : relayOf l s ≡ relayOf l s′ → phOf l s ≡ phOf l s′
             → cellDn l s ≡ cellDn l s′ → dnClient l s ≡ dnClient l s′
             → ProdNotSent (prodOf l s) → ProdSent (prodOf l s′)
             → PipeStep⁺ l s s′
  -- relay internal hop (class-preserving)
  psRelayMove : prodOf l s ≡ prodOf l s′ → phOf l s ≡ phOf l s′
              → cellUp l s ≡ cellUp l s′ → cellDn l s ≡ cellDn l s′
              → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
              → (RelayPre (relayOf l s) → RelayPre (relayOf l s′))
              → (RelayHas (relayOf l s) → RelayHas (relayOf l s′))
              → (RelayFwd (relayOf l s) → RelayFwd (relayOf l s′))
              → PipeStep⁺ l s s′
  -- relay forward (`sendBFBlock` onward, `L2 → L3`)
  psRelayFwd : prodOf l s ≡ prodOf l s′ → phOf l s ≡ phOf l s′
             → cellUp l s ≡ cellUp l s′ → upClient l s ≡ upClient l s′
             → RelayHas (relayOf l s) → RelayFwd (relayOf l s′)
             → PipeStep⁺ l s s′
  -- relay receive (`recvBFBlock`, `L1 → L2`)
  psRelayRecv : prodOf l s ≡ prodOf l s′ → phOf l s ≡ phOf l s′
              → cellUp l s ≡ cellUp l s′ → cellDn l s ≡ cellDn l s′
              → dnClient l s ≡ dnClient l s′
              → RelayPre (relayOf l s) → BFcHasBlk (upClient l s)
              → RelayHas (relayOf l s′) → PipeStep⁺ l s s′
  -- consumer internal hop (class-preserving)
  psConsMove : prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
             → cellUp l s ≡ cellUp l s′ → cellDn l s ≡ cellDn l s′
             → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
             → (InCp03 (phOf l s) → InCp03 (phOf l s′))
             → (ConsRecv (phOf l s) → ConsRecv (phOf l s′))
             → PipeStep⁺ l s s′
  -- consumer receive (`recvBFBlock`, `L3 → L4`)
  psConsRecv : prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
             → cellUp l s ≡ cellUp l s′ → cellDn l s ≡ cellDn l s′
             → upClient l s ≡ upClient l s′
             → InCp03 (phOf l s) → BFcHasBlk (dnClient l s)
             → ConsRecv (phOf l s′) → PipeStep⁺ l s s′
  -- WEAK-move preservation carrier: a whole weak visible move `s ↝ s′` pads its
  -- visible middle with ARBITRARY hidden-io τ hand-offs on both sides (cells
  -- fill/drain, BF clients advance while the drivers stay fixed), which no single
  -- fine-step ctor matches (a pure io hand-off moves a cell/client with the
  -- drivers fixed).  Rather than a granularity-mismatched single class, `stepEmit`
  -- FOLDS the fine steps of the move — composing the io hand-off cores
  -- (`PipeIoHandoff`) and the visible-middle driver cores left-to-right — into ONE
  -- preservation map, carried here directly.  `pipeInv⁺-step (psWeak f) = f`.
  psWeak : (PipeInv⁺ l s → PipeInv⁺ l s′) → PipeStep⁺ l s s′

-- TOTAL dispatcher: a classified step preserves `PipeInv⁺` (each clause is the
-- matching core above)
pipeInv⁺-step : (l : TwoLegs) (s s′ : SysState)
              → PipeStep⁺ l s s′ → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-step l s s′ (psFrame pe re ce cue cde ue de) =
  pipeInv⁺-frame l s s′ pe re ce cue cde ue de
pipeInv⁺-step l s s′ (psProdMove re ce cue cde ue de fN fS) =
  pipeInv⁺-prod-move l s s′ re ce cue cde ue de fN fS
pipeInv⁺-step l s s′ (psProdSend re ce cde de nN sS) =
  pipeInv⁺-prod-send l s s′ re ce cde de nN sS
pipeInv⁺-step l s s′ (psRelayMove pe ce cue cde ue de fP fH fF) =
  pipeInv⁺-relay-move l s s′ pe ce cue cde ue de fP fH fF
pipeInv⁺-step l s s′ (psRelayFwd pe ce cue ue hHas hFwd) =
  pipeInv⁺-relay-fwd l s s′ pe ce cue ue hHas hFwd
pipeInv⁺-step l s s′ (psRelayRecv pe ce cue cde de hrPre hUp hHas′) =
  pipeInv⁺-relay-recv l s s′ pe ce cue cde de hrPre hUp hHas′
pipeInv⁺-step l s s′ (psConsMove pe re cue cde ue de fI fR) =
  pipeInv⁺-cons-move l s s′ pe re cue cde ue de fI fR
pipeInv⁺-step l s s′ (psConsRecv pe re cue cde ue hPre hDn hRecv′) =
  pipeInv⁺-cons-recv l s s′ pe re cue cde ue hPre hDn hRecv′
-- the weak-move carrier applies its already-composed preservation map directly
pipeInv⁺-step l s s′ (psWeak f) = f

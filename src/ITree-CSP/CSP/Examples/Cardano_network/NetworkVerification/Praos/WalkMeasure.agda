{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the WALK MEASURE (`Praos.WalkMeasure`).
--
-- R3 delivers the abstract-system liveness walk
--   `abstractLive : ∀ b → abstractSystem ⊨ᵂ respondsAtoD b`.
-- Its well-founded core is a `μ_D`-descent argument: block `b`, once produced
-- at A, is delivered to D in finitely many steps because a delivery-distance
-- measure strictly decreases along the intact relay pipeline and there is
-- nothing else (RISK-A verdict: FORCED — no fairness) that can stall it.
--
-- THIS MODULE builds the structural foundation of that descent, over the R2
-- reachable-config subtype `RState` (`Praos.SysReach`), whose abstract decode
-- `radec r = absDec (toSys r)` uses the SHARED driver phases (`decProd`/
-- `decCons`/`decCP`/`decConsD`) and the SHARED breakable medium — so a measure
-- read off the underlying `SysState` is a measure on the abstract config.
--
-- The DELIVERY PIPELINE for block `b` down a confinement group is a linear
-- chain of api handshakes: since the operative model gates ALL api channels
-- (`apiSet = ⊤`, FourNodeDiamond:154-162), every driven peer moves ONLY in
-- lock-step with a driver api event, so the driver phases are the master clock
-- of forward progress.  Group 1 = {AB, BD} routes A→B→D, driven by A's
-- `produce linkAB hi` (`prod-AB`), B's relay `consume linkAB >>= produce linkBD`
-- (`cp-B`) and D's `consume linkBD` (`cons-BD`); group 2 = {AC, CD} routes
-- A→C→D, driven by `prod-AC`, C's `cp-C` and D's `cons-CD`.
--
-- `μG1`/`μG2` are the PER-GROUP driver delivery-distances (remaining
-- driver-script events to D's `recvBFBlock`).  We expose them per-group rather
-- than combined, because `confined` selects ONE intact group and it is THAT
-- group's measure the walk descends (a break on the other group is measure-
-- neutral — it touches no driver of the intact group; a break on the intact
-- group is refuted by the confinement disjunct — both are Walk.agda's job).
--
-- INERTNESS is the RISK-A crux fact, here as a STRUCTURAL invariance:
-- `μG1`/`μG2` read ONLY their group's three driver phases — never the inert
-- KA/TS/LN/LF peer positions, never the CS/BF peer positions, never the
-- medium, never the other group.  So `μGk-cong` says any change confined to
-- those fields leaves the measure fixed: the inert peers contribute NO forward
-- measure progress, exactly the "no competing enabled action" fact.
--
-- No postulates, holes, or `--allow-unsolved-metas`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; +-monoˡ-<; +-monoʳ-<)
open import Data.List using (List; []; _∷_; map; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; cong₂)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkMeasure (blkA : Block₃) where

------------------------------------------------------------------------
-- The concrete model + the R1/R2 state and reachable-config machinery.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi; IDs )
open import CSP.Examples.Cardano_network.Net p using ( Link )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks; linkConfig )

-- the medium abstract state: per-cell `CopyPhase` + per-link break flag
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( MedState; mkMed; phase; broken
        ; CopyPhase; empty; full; draining )
-- the driver phases + node states (the abstract config's shared drivers)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; CPPh; consuming; producing
        ; ConsDPh; consD; cblk; cph
        ; NodeStateA; NodeStateB; NodeStateC; NodeStateD
        ; prod-AB; prod-AC; cp-B; cp-C; cons-BD; cons-CD )
-- the whole-system state + its reachable subtype
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; initial )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; toSys; rinit )

------------------------------------------------------------------------
-- Per-driver remaining-work weights (the master api clock).
--
-- Each driver is a finite linear api-script; its weight is the number of
-- forward api events still to fire.  Consecutive phases have consecutive
-- weights, so every single-event advance strictly decreases the weight by 1.
------------------------------------------------------------------------

-- `produce` remaining events (9-event body; `pp9 = Skip` is done)
prodW : ProdPh → ℕ
prodW pp0 = 9
prodW pp1 = 8
prodW pp2 = 7
prodW pp3 = 6
prodW pp4 = 5
prodW pp5 = 4
prodW pp6 = 3
prodW pp7 = 2
prodW pp8 = 1
prodW pp9 = 0

-- `consume` remaining events (6-event body; `cp6 = Ret` is done).  D's block
-- receipt `recvBFBlock` (= `arrivedD`) is the `cp3 → cp4` event, so weight ≤ 2
-- means D has already received the block.
consW : ConsPh → ℕ
consW cp0 = 6
consW cp1 = 5
consW cp2 = 4
consW cp3 = 3
consW cp4 = 2
consW cp5 = 1
consW cp6 = 0

-- relay `consume l₁ >>= produce l₂` remaining events: while consuming, the
-- produce leg (9 events) is still ahead of the consume remainder (offset +10 so
-- the `consuming cp6 → producing pp0` bind hop is itself a strict decrease
-- 10 > 9); while producing, just the produce remainder.
cpW : CPPh → ℕ
cpW (consuming _ c) = 10 + consW c
cpW (producing _ p) = prodW p

-- node-D consume remaining events (the stored block is measure-irrelevant)
consDW : ConsDPh → ℕ
consDW (consD _ c) = consW c

------------------------------------------------------------------------
-- Per-cell / per-link medium in-flight weight (the SECONDARY component).
--
-- A copy cell carrying a payload contributes to the delivery distance: `full`
-- has two wire hops left (output-to-receiver, then loop-back), `draining` one,
-- `empty` none.  `medLinkInflight` sums the configured cells of one link.
--
-- NOTE (reported frontier): a wire `fill` hop (empty→full, a hidden io-sync)
-- INCREASES this count, so `medInflight` is NOT monotone on its own — the
-- fill's forward progress is "paid for" only jointly with the enabling driver
-- send.  A monotone whole-pipeline measure needs a block-POSITION invariant
-- (which cell currently carries `b`), threaded by Walk.agda; here we expose
-- the cell arithmetic and keep the SOUND monotone core in the driver weights.
------------------------------------------------------------------------

-- one copy cell's in-flight weight
cellW : CopyPhase → ℕ
cellW empty        = 0
cellW (full _)     = 2
cellW (draining _) = 1

-- the in-flight weight of one link's configured cells
medLinkInflight : MedState → Link → ℕ
medLinkInflight m l =
  foldr (λ dq acc → cellW (phase m l (proj₁ dq) (proj₂ dq)) + acc) 0 (linkConfig l)

------------------------------------------------------------------------
-- The per-group driver delivery-distance (the SOUND, MONOTONE measure).
------------------------------------------------------------------------

-- group 1 (A→B→D over links AB, BD): A's produce, B's relay, D's consume
μG1 : SysState → ℕ
μG1 s = prodW (prod-AB (nA s)) + (cpW (cp-B (nB s)) + consDW (cons-BD (nD s)))

-- group 2 (A→C→D over links AC, CD): A's produce, C's relay, D's consume
μG2 : SysState → ℕ
μG2 s = prodW (prod-AC (nA s)) + (cpW (cp-C (nC s)) + consDW (cons-CD (nD s)))

-- the measures on the reachable-config subtype (the abstract-walk domain)
μ_D-G1 : Block₃ → RState → ℕ
μ_D-G1 _ r = μG1 (toSys r)

μ_D-G2 : Block₃ → RState → ℕ
μ_D-G2 _ r = μG2 (toSys r)

------------------------------------------------------------------------
-- INERTNESS (RISK-A crux, structural form): the measure reads ONLY its
-- group's three driver phases.  Any change confined to the inert KA/TS/LN/LF
-- peers, the driven CS/BF peers, the medium, or the OTHER group preserves it.
------------------------------------------------------------------------

-- `μG1` depends only on `prod-AB`, `cp-B`, `cons-BD` — nothing else
μG1-cong : (s s′ : SysState)
         → prod-AB (nA s) ≡ prod-AB (nA s′)
         → cp-B (nB s)  ≡ cp-B (nB s′)
         → cons-BD (nD s) ≡ cons-BD (nD s′)
         → μG1 s ≡ μG1 s′
μG1-cong s s′ ep ec ed =
  cong₂ (λ a bc → prodW a + bc)
        ep
        (cong₂ (λ b c → cpW b + consDW c) ec ed)

-- `μG2` depends only on `prod-AC`, `cp-C`, `cons-CD` — nothing else
μG2-cong : (s s′ : SysState)
         → prod-AC (nA s) ≡ prod-AC (nA s′)
         → cp-C (nC s)  ≡ cp-C (nC s′)
         → cons-CD (nD s) ≡ cons-CD (nD s′)
         → μG2 s ≡ μG2 s′
μG2-cong s s′ ep ec ed =
  cong₂ (λ a bc → prodW a + bc)
        ep
        (cong₂ (λ b c → cpW b + consDW c) ec ed)

------------------------------------------------------------------------
-- DELIVERED characterisation: `μ = 0` on a group forces D past `recvBFBlock`
-- on that group — i.e. `arrivedD` has already fired (D's consume is at `cp6`,
-- strictly beyond the `cp3 → cp4` `recvBFBlock` = `arrivedD` event).
------------------------------------------------------------------------

-- a zero sum has a zero right summand
+≡0-r : (m n : ℕ) → m + n ≡ 0 → n ≡ 0
+≡0-r zero    n eq = eq
+≡0-r (suc m) n ()

-- only the final consume phase `cp6` has zero remaining weight
consW≡0→cp6 : (c : ConsPh) → consW c ≡ 0 → c ≡ cp6
consW≡0→cp6 cp6 refl = refl
consW≡0→cp6 cp0 ()
consW≡0→cp6 cp1 ()
consW≡0→cp6 cp2 ()
consW≡0→cp6 cp3 ()
consW≡0→cp6 cp4 ()
consW≡0→cp6 cp5 ()

-- `μG1 s ≡ 0` forces D's consume on link BD to the final phase `cp6` — the
-- block was received (`recvBFBlock` = `arrivedD` fires at `cp3 → cp4`, before
-- `cp6`), so `arrivedD` has already occurred along B→D.  (`consDW (cons-BD) ≡
-- consW (cph (cons-BD))` by record η; two `+≡0-r`s peel the sum to it.)
μG1-zero→cp6 : (s : SysState) → μG1 s ≡ 0 → cph (cons-BD (nD s)) ≡ cp6
μG1-zero→cp6 s eq =
  consW≡0→cp6 (cph (cons-BD (nD s)))
    (+≡0-r (cpW (cp-B (nB s))) (consDW (cons-BD (nD s)))
       (+≡0-r (prodW (prod-AB (nA s))) (cpW (cp-B (nB s)) + consDW (cons-BD (nD s))) eq))

-- symmetric for group 2 (C→D)
μG2-zero→cp6 : (s : SysState) → μG2 s ≡ 0 → cph (cons-CD (nD s)) ≡ cp6
μG2-zero→cp6 s eq =
  consW≡0→cp6 (cph (cons-CD (nD s)))
    (+≡0-r (cpW (cp-C (nC s))) (consDW (cons-CD (nD s)))
       (+≡0-r (prodW (prod-AC (nA s))) (cpW (cp-C (nC s)) + consDW (cons-CD (nD s))) eq))

------------------------------------------------------------------------
-- PER-HOP DRIVER DECREASE — the strict-descent facts for the driven forward
-- steps (produce advance, relay advance, D-consume advance).
--
-- Each driver's single-event advance is a per-phase adjacency; consecutive
-- weights differ by 1, so the strict decrease is `≤-refl` at the base and
-- `+-monoˡ-<` / `+-monoʳ-<` for the summand it sits in.
------------------------------------------------------------------------

-- one-event `produce` advance (the 9 adjacencies of the linear script)
data ProdAdv : ProdPh → ProdPh → Set where
  a01 : ProdAdv pp0 pp1
  a12 : ProdAdv pp1 pp2
  a23 : ProdAdv pp2 pp3
  a34 : ProdAdv pp3 pp4
  a45 : ProdAdv pp4 pp5
  a56 : ProdAdv pp5 pp6
  a67 : ProdAdv pp6 pp7
  a78 : ProdAdv pp7 pp8
  a89 : ProdAdv pp8 pp9

-- a `produce` advance strictly decreases the produce weight
prodW-adv : {p p′ : ProdPh} → ProdAdv p p′ → prodW p′ < prodW p
prodW-adv a01 = ≤-refl
prodW-adv a12 = ≤-refl
prodW-adv a23 = ≤-refl
prodW-adv a34 = ≤-refl
prodW-adv a45 = ≤-refl
prodW-adv a56 = ≤-refl
prodW-adv a67 = ≤-refl
prodW-adv a78 = ≤-refl
prodW-adv a89 = ≤-refl

-- one-event `consume` advance (the 6 adjacencies of the linear script)
data ConsAdv : ConsPh → ConsPh → Set where
  c01 : ConsAdv cp0 cp1
  c12 : ConsAdv cp1 cp2
  c23 : ConsAdv cp2 cp3
  c34 : ConsAdv cp3 cp4   -- this is D's `recvBFBlock` = `arrivedD`
  c45 : ConsAdv cp4 cp5
  c56 : ConsAdv cp5 cp6

-- a `consume` advance strictly decreases the consume weight
consW-adv : {c c′ : ConsPh} → ConsAdv c c′ → consW c′ < consW c
consW-adv c01 = ≤-refl
consW-adv c12 = ≤-refl
consW-adv c23 = ≤-refl
consW-adv c34 = ≤-refl
consW-adv c45 = ≤-refl
consW-adv c56 = ≤-refl

-- one-event relay advance: consume-side advance, the consume→produce bind
-- boundary, or produce-side advance
data CPAdv : CPPh → CPPh → Set where
  cpC   : ∀ {b c c′} → ConsAdv c c′ → CPAdv (consuming b c) (consuming b c′)
  cpB   : ∀ {b b′}   → CPAdv (consuming b cp6) (producing b′ pp0)  -- >>= bind hop
  cpP   : ∀ {b p p′} → ProdAdv p p′ → CPAdv (producing b p) (producing b p′)

-- a relay advance strictly decreases the relay weight
cpW-adv : {x x′ : CPPh} → CPAdv x x′ → cpW x′ < cpW x
cpW-adv (cpC ca) = +-monoʳ-< 10 (consW-adv ca)   -- 10 + consW c′ < 10 + consW c
cpW-adv cpB      = ≤-refl                          -- 9 < 10
cpW-adv (cpP pa) = prodW-adv pa

-- a node-D consume advance strictly decreases `consDW` (stored block is free)
consDW-adv : {b b′ : Block₃} {c c′ : ConsPh}
           → ConsAdv c c′ → consDW (consD b′ c′) < consDW (consD b c)
consDW-adv ca = consW-adv ca

------------------------------------------------------------------------
-- Lifting the per-driver decreases to the group measure `μG1`/`μG2`.
--
-- Each lemma takes the advancing driver's `Adv` witness and equalities of the
-- other two drivers of the group; `μGk` strictly decreases.
------------------------------------------------------------------------

-- group 1, A's produce advances (other two drivers fixed)
μG1-adv-prod : (s s′ : SysState)
             → ProdAdv (prod-AB (nA s)) (prod-AB (nA s′))
             → cp-B (nB s) ≡ cp-B (nB s′)
             → cons-BD (nD s) ≡ cons-BD (nD s′)
             → μG1 s′ < μG1 s
μG1-adv-prod s s′ pa ec ed
  rewrite ec | ed = +-monoˡ-< (cpW (cp-B (nB s′)) + consDW (cons-BD (nD s′))) (prodW-adv pa)

-- group 1, B's relay advances (produce + D-consume fixed)
μG1-adv-cp : (s s′ : SysState)
           → prod-AB (nA s) ≡ prod-AB (nA s′)
           → CPAdv (cp-B (nB s)) (cp-B (nB s′))
           → cons-BD (nD s) ≡ cons-BD (nD s′)
           → μG1 s′ < μG1 s
μG1-adv-cp s s′ ep ca ed
  rewrite ep | ed = +-monoʳ-< (prodW (prod-AB (nA s′)))
                      (+-monoˡ-< (consDW (cons-BD (nD s′))) (cpW-adv ca))

-- group 1, D's consume advances (produce + relay fixed)
μG1-adv-cons : (s s′ : SysState)
             → prod-AB (nA s) ≡ prod-AB (nA s′)
             → cp-B (nB s) ≡ cp-B (nB s′)
             → ConsAdv (cph (cons-BD (nD s))) (cph (cons-BD (nD s′)))
             → μG1 s′ < μG1 s
μG1-adv-cons s s′ ep ec ca
  rewrite ep | ec = +-monoʳ-< (prodW (prod-AB (nA s′)))
                      (+-monoʳ-< (cpW (cp-B (nB s′))) (consW-adv ca))

-- group 2, A's produce advances
μG2-adv-prod : (s s′ : SysState)
             → ProdAdv (prod-AC (nA s)) (prod-AC (nA s′))
             → cp-C (nC s) ≡ cp-C (nC s′)
             → cons-CD (nD s) ≡ cons-CD (nD s′)
             → μG2 s′ < μG2 s
μG2-adv-prod s s′ pa ec ed
  rewrite ec | ed = +-monoˡ-< (cpW (cp-C (nC s′)) + consDW (cons-CD (nD s′))) (prodW-adv pa)

-- group 2, C's relay advances
μG2-adv-cp : (s s′ : SysState)
           → prod-AC (nA s) ≡ prod-AC (nA s′)
           → CPAdv (cp-C (nC s)) (cp-C (nC s′))
           → cons-CD (nD s) ≡ cons-CD (nD s′)
           → μG2 s′ < μG2 s
μG2-adv-cp s s′ ep ca ed
  rewrite ep | ed = +-monoʳ-< (prodW (prod-AC (nA s′)))
                      (+-monoˡ-< (consDW (cons-CD (nD s′))) (cpW-adv ca))

-- group 2, D's consume advances
μG2-adv-cons : (s s′ : SysState)
             → prod-AC (nA s) ≡ prod-AC (nA s′)
             → cp-C (nC s) ≡ cp-C (nC s′)
             → ConsAdv (cph (cons-CD (nD s))) (cph (cons-CD (nD s′)))
             → μG2 s′ < μG2 s
μG2-adv-cons s s′ ep ec ca
  rewrite ep | ec = +-monoʳ-< (prodW (prod-AC (nA s′)))
                      (+-monoʳ-< (cpW (cp-C (nC s′))) (consW-adv ca))

------------------------------------------------------------------------
-- The measure at the initial reachable config (sanity endpoints).
------------------------------------------------------------------------

-- at `initial` both groups are at full distance: produce `pp0` (9) + relay
-- `consuming blkA cp0` (10+6=16) + D-consume `cp0` (6) = 31
μG1-init : μG1 initial ≡ 31
μG1-init = refl

μG2-init : μG2 initial ≡ 31
μG2-init = refl

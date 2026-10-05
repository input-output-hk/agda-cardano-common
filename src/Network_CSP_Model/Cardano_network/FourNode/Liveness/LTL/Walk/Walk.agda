{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the WALK (`Praos.Walk`).
--
-- R3's target is
--   `abstractLive : ∀ b → abstractSystem ⊨ᵂ respondsAtoD b`
-- (classical `confined ⇒ G (producedA b ⇒ F (arrivedD b))`).  Its positive
-- core is a well-founded descent: block `b`, once produced at A, reaches D in
-- finitely many observable steps.  `Praos.WalkMeasure` built the PER-GROUP
-- driver delivery-distances `μG1`/`μG2` (each strictly ↓ on a driven forward
-- api event of its group).  THIS module builds the WHOLE-TRACE well-founded
-- measure the walk actually descends and records the two architectural facts
-- that reshape the reported obstruction.
--
-- ────────────────────────────────────────────────────────────────────
-- FINDING 1 — the reported "block-POSITION" obstruction DISSOLVES at the
-- observable-step (`WTrace`) level, so no medium-cell position invariant is
-- needed for the per-step descent.
--
-- A `WTrace` `step` (`Semantics.LTL.WTrace`, ctor `step`) is a *weak visible*
-- transition `t ═[ ev e ]═► t′`, i.e. `τ* · (ev e) · τ*`: the hidden io-sync
-- τ's (medium fill `empty→full`, drain `full→draining`, loop-back
-- `draining→empty`, and peer receive-sils) are ABSORBED into the padding of a
-- single observable step.  They are NOT separate walk frames.  Hence the
-- measure walkPos descends per `step` is the DRIVER measure — the medium in-
-- flight count (`WalkMeasure.medLinkInflight`, non-monotone because a fill
-- +2's it) never appears as the descent variable.  A weak step's net driver
-- effect is exactly the effect of its single middle visible event:
--   · an intact-group api handshake (produce / relay / D-consume) advances one
--     driver phase ⇒ `μG_k` strictly ↓ (WalkMeasure `μGk-adv-*`); the io-sync
--     τ-padding is driver-NEUTRAL (WalkMeasure `μGk-cong` — the measure reads
--     only the three group drivers, never a medium cell or a peer position);
--   · an other-group api advances that group's driver ⇒ `μG_(other)` ↓;
--   · a `break` on the other group ↓'s the break budget (below);
--   · a `break` on the intact group is refuted by the `confined` disjunct.
-- So the per-step descent variable is `μTot` (below), a SINGLE ℕ that strictly
-- decreases on EVERY observable step class — giving that a maximal `WTrace`
-- from a produced state has only FINITELY many `step`s before a terminal
-- (`done` / `stuck` / `div`) frame.
--
-- ────────────────────────────────────────────────────────────────────
-- FINDING 2 — the TRUE remaining crux is τ-CONVERGENCE (divergence-freedom),
-- NOT the block position.
--
-- `arrivedD b` (spec `FourNodeDiamondLiveness`) holds ONLY on a `step` frame
-- carrying `apiBF … recvBFBlock`; on a `div` / `stuck` / `done` frame it is
-- `⊥`.  So after the finitely-many `step`s (Finding 1) the walk lands on a
-- terminal frame, and it must EXCLUDE the two non-delivering terminals:
--   · `div  : Diverges (radec r) → WTrace …` — a silent infinite τ-chain emits
--     NO visible event, so it can never satisfy `arrivedD`.  Excluding it needs
--     `¬ Diverges (radec r)` for the (pending, confined) reachable `r`.
--   · `stuck` before `μG_k = 0` — refuted by ENABLEDNESS: the intact relay's
--     next hop is enabled (RISK-A verdict FORCED — inert peers offer nothing).
-- `¬ Diverges (radec r)` is EXACTLY the τ-convergence obstruction R2 left OPEN:
-- R2's `odiv←`/`odiv→` were discharged by a *coinductive transfer*
-- (`SysBisim.divChain`), NOT by refuting `Diverges` (SysBisim:505-510 records
-- the measure `μ` as only the "intended" vehicle; "μ obstruction confirmed",
-- progress 2026-08-03).  `μ`/`μ'` count only peer sils, never the medium
-- cells, and a fill +2's the in-flight count — so no existing measure is
-- WF-decreasing on every hidden τ.  The block-POSITION invariant (which cell
-- holds each in-flight payload, decodable from the `full x`/`draining x`
-- payload, so a fill moves the payload strictly downstream) is the measure that
-- WOULD close it — but it lives on the HIDDEN-τ layer, feeding `¬ Diverges`,
-- NOT the observable-step descent.  Building it requires the heavy SysRoute/
-- SysOracle per-τ-class inversion cone (RISK-C RAM).  See the frontier note in
-- `.superpowers/sdd/r3-plan.md`.
--
-- ────────────────────────────────────────────────────────────────────
-- THIS module (LIGHT — the `SysReach`/`WalkMeasure` cone only, no SysOracle):
-- the whole-trace measure `μTot = μG1 + μG2 + breakBudget` and its per-class
-- strict-descent lemmas (a G1 driver advance, a G2 driver advance, and a break
-- each strictly ↓ `μTot`, the other two components held fixed).  These are the
-- arithmetic obligations walkPos discharges once the step-lift supplies which
-- component moved.  No postulates, holes, or unsolved metas.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl; +-monoˡ-<; +-monoʳ-<; +-mono-<-≤; +-mono-≤-<)
open import Data.Bool using (Bool; true; false; not)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk (blkA : Block₃) where

------------------------------------------------------------------------
-- The model links, the state, the medium, and the driver measures.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using ( Link )
-- the whole-system state and its medium projection
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; initial )
-- the medium abstract state: per-link break flags
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; broken; initMed )
-- the per-group driver delivery-distances (the SOUND monotone core)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( μG1; μG2; μG1-init; μG2-init )

------------------------------------------------------------------------
-- The BREAK BUDGET — the finite fuel of the (other-group) break events.
--
-- Each link breaks at most once (its `broken` flag flips `false → true`), so
-- the count of still-unbroken links is a strictly-decreasing budget for the
-- observable `break` events.  Summing all four diamond links keeps the measure
-- group-agnostic: the walk descends it whichever group is intact (the
-- intact-group break is refuted by `confined`, so only OTHER-group breaks are
-- ever taken, but the budget bounds them either way).
------------------------------------------------------------------------

-- Bool → ℕ: an unbroken flag is worth 1, a broken flag 0
b2n : Bool → ℕ
b2n true  = 1
b2n false = 0

-- one link's remaining break fuel (1 while unbroken, 0 once broken)
linkBudget : MedState → Link → ℕ
linkBudget m l = b2n (not (broken m l))

-- the break budget: the number of the four diamond links still unbroken
breakBudget : MedState → ℕ
breakBudget m =
  linkBudget m linkAB + (linkBudget m linkAC + (linkBudget m linkBD + linkBudget m linkCD))

------------------------------------------------------------------------
-- THE WHOLE-TRACE MEASURE `μTot` (the per-observable-step descent variable).
--
-- `μTot = μG1 + μG2 + breakBudget`.  Every observable-step class strictly
-- decreases exactly ONE summand while the other two stay fixed (a single
-- visible api advances one group's driver; a `break` flips one link's flag),
-- so `μTot` strictly decreases on every `WTrace` `step` — the well-founded
-- ranking that bounds the number of steps before a terminal frame.
------------------------------------------------------------------------

-- the whole-trace measure
μTot : SysState → ℕ
μTot s = μG1 s + (μG2 s + breakBudget (med s))

------------------------------------------------------------------------
-- PER-CLASS STRICT DESCENT — the arithmetic obligations walkPos discharges
-- once step-lift says which component moved.  Each lemma takes the moving
-- component's strict decrease and the other two components' fixity.
------------------------------------------------------------------------

-- a group-1 driver advance (μG1 ↓, μG2 and break budget fixed) ↓'s μTot
μTot-adv-G1 : (s s′ : SysState)
            → μG1 s′ < μG1 s
            → μG2 s′ ≡ μG2 s
            → breakBudget (med s′) ≡ breakBudget (med s)
            → μTot s′ < μTot s
μTot-adv-G1 s s′ lt e2 eb rewrite e2 | eb =
  +-mono-<-≤ lt (≤-refl {μG2 s + breakBudget (med s)})

-- a group-2 driver advance (μG2 ↓, μG1 and break budget fixed) ↓'s μTot
μTot-adv-G2 : (s s′ : SysState)
            → μG1 s′ ≡ μG1 s
            → μG2 s′ < μG2 s
            → breakBudget (med s′) ≡ breakBudget (med s)
            → μTot s′ < μTot s
μTot-adv-G2 s s′ e1 lt eb rewrite e1 | eb =
  +-monoʳ-< (μG1 s) (+-mono-<-≤ lt (≤-refl {breakBudget (med s)}))

-- a break event (break budget ↓, both group measures fixed) ↓'s μTot
μTot-break : (s s′ : SysState)
           → μG1 s′ ≡ μG1 s
           → μG2 s′ ≡ μG2 s
           → breakBudget (med s′) < breakBudget (med s)
           → μTot s′ < μTot s
μTot-break s s′ e1 e2 lt rewrite e1 | e2 =
  +-monoʳ-< (μG1 s) (+-monoʳ-< (μG2 s) lt)

------------------------------------------------------------------------
-- The measure at the initial reachable config (sanity endpoint): both groups
-- at full distance (31 each, `WalkMeasure.μGk-init`) and all four links
-- unbroken (break budget 4) give `μTot initial ≡ 66`.
------------------------------------------------------------------------

-- `breakBudget initMed ≡ 4` (all four links unbroken at the initial medium)
breakBudget-init : breakBudget initMed ≡ 4
breakBudget-init = refl

-- `μTot initial ≡ 66` (31 + 31 + 4)
μTot-init : μTot initial ≡ 66
μTot-init = cong₂ (λ a bc → a + bc) μG1-init (cong₂ (λ b c → b + c) μG2-init breakBudget-init)

------------------------------------------------------------------------
-- THE CLASSICAL WRAPPER `respondsᵂ-intro` + `abstractLive`.
--
-- Reduces the R3 target
--   `abstractLive : ∀ b → abstractSystem ⊨ᵂ respondsAtoD b`
-- — the CLASSICAL `confined ⇒ G (producedA ⇒ F arrivedD)` in the WTrace
-- semantics `⟦_⟧ᵂ` — to the POSITIVE walk `walkPos` (a MODULE PARAMETER here:
-- the remaining R3 crux, the well-founded delivery descent over `μTot`).
--
-- This mirrors `Semantics.LTL.ClassicalDescent` but in the INTRO direction
-- (positive → classical) and on the WTrace `⟦_⟧ᵂ` layer.  ClassicalDescent's
-- descent (classical → positive) needed exactly one classical step,
-- `¬¬F⇒F`.  The INTRO direction needs the GENERAL certified `dne` (the SAME
-- campaign axiom, `Classical.dne`, from which `¬¬F⇒F` is itself certified —
-- NOT a fresh postulate): (i) to split the CLASSICAL `∨` confinement
-- `⟦ (G ¬brkG1) ∨ (G ¬brkG2) ⟧ᵂ` into the POSITIVE `⊎` group-selection
-- `walkPos` consumes (the ∨-split is genuinely not derivable from the
-- F-modality axiom alone), and (ii) to extract the positive `producedA` from
-- its double negation.  The `G → ⟦G⟧⁺` direction is CONSTRUCTIVE here because
-- the confinement subformulas `¬ atom brkGᵢ` are negations.
--
-- Parameterising over `walkPos` follows the `WalkConv` engine pattern
-- (`absNoDiv` was delivered parameterised over `μτ`/`τreflect`, then those
-- were instantiated): the classical endgame is now fully de-risked and the
-- ENTIRE remaining R3 obligation is the single positive-walk hypothesis.
------------------------------------------------------------------------

open import Level using ( 0ℓ; Lift; lift; lower )
open import Data.Empty using ( ⊥ )
open import Data.Unit.Polymorphic using ( ⊤ )
import Data.Unit as U
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Product using ( Σ; _,_; _×_ )
open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( LTLᵗ; FramePred; atom; ¬_; _∧_; _∨_; _⇒_; F_; G_; _U_; ⊤' )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; ⟦_⟧ᵂ; drop; _⊨ᵂ_ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA; arrivedD; brkG1; brkG2; confined; respondsAtoD )

-- the campaign's SINGLE certified classical axiom (≡ LEM); `¬¬F⇒F` of
-- `ClassicalDescent` is itself certified from this in `ClassicalFromLEM`
open import Classical using ( dne )

-- the whole-system process type at the shared alphabet
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the WTrace-layer positive "globally" (pointwise): φ holds at every suffix
G⁺ᵂ : {t : NetProc} → LTLᵗ 0ℓ (⊤ {0ℓ}) → WTrace (⊤ {0ℓ}) t → Set
G⁺ᵂ φ tr = ∀ m → ⟦ φ ⟧ᵂ (drop m tr)

-- `⟦ G_ (¬ atom P) ⟧ᵂ ⇒ ⟦G⟧⁺ᵂ (¬ atom P)` — CONSTRUCTIVE, no `dne`, because
-- the subformula `¬ atom P` is a negation: feed the pointwise `atom P` witness
-- into the `F (¬ ¬ atom P)` refuter as a one-cell `U`-witness.
G→G⁺-neg : (P : FramePred 0ℓ (⊤ {0ℓ})) {t : NetProc} (tr : WTrace (⊤ {0ℓ}) t)
         → ⟦ G_ (¬ atom P) ⟧ᵂ tr → G⁺ᵂ (¬ atom P) tr
G→G⁺-neg P tr g m pm = g (m , (λ notP → notP pm) , (λ _ _ → lift U.tt))

-- extract the positive `producedA` from its double negation (a single `dne`)
getProd : (b : Block₃) {t : NetProc} (tr : WTrace (⊤ {0ℓ}) t)
        → ⟦ ¬ ¬ atom (producedA b) ⟧ᵂ tr → ⟦ atom (producedA b) ⟧ᵂ tr
getProd b tr nnp = dne (λ notp → lower (nnp (λ pv → lift (notp pv))))

-- split the classical `∨` confinement into the positive `⊎` (a single `dne`)
conf⊎ : {t : NetProc} (tr : WTrace (⊤ {0ℓ}) t)
      → ⟦ ¬ ¬ confined ⟧ᵂ tr
      → (G⁺ᵂ (¬ atom brkG1) tr ⊎ G⁺ᵂ (¬ atom brkG2) tr)
conf⊎ tr nnconf =
  dne (λ no⊎ →
    lower (nnconf (λ cf →
      cf ( (λ g1 → lift (no⊎ (inj₁ (G→G⁺-neg brkG1 tr g1))))
         , (λ g2 → lift (no⊎ (inj₂ (G→G⁺-neg brkG2 tr g2)))) ))))

------------------------------------------------------------------------
-- Parameterised over the positive walk (the remaining R3 crux).
------------------------------------------------------------------------

module _
  (walkPos : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem)
           → (G⁺ᵂ (¬ atom brkG1) tr ⊎ G⁺ᵂ (¬ atom brkG2) tr)
           → ∀ n → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
           → ⟦ F_ (atom (arrivedD b)) ⟧ᵂ (drop n tr))
  where

  -- classical INTRO: the positive walk yields the classical `respondsAtoD`
  respondsᵂ-intro : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem)
                  → ⟦ respondsAtoD b ⟧ᵂ tr
  respondsᵂ-intro b tr (nnconf , nB) = nB bB
    where
      -- `⟦ G (producedA ⇒ F arrivedD) ⟧ᵂ tr` — refute any `F (¬ (p ⇒ F q))`
      bB : ⟦ G_ ((atom (producedA b)) ⇒ (F_ (atom (arrivedD b)))) ⟧ᵂ tr
      bB (n , nφ , _) =
        nφ (λ { (nnp , nFq) →
                  nFq (walkPos b tr (conf⊎ tr nnconf) n (getProd b (drop n tr) nnp)) })

  -- R3 TARGET: the abstract system classically satisfies `respondsAtoD`
  abstractLive : (b : Block₃) → abstractSystem ⊨ᵂ respondsAtoD b
  abstractLive b tr = respondsᵂ-intro b tr

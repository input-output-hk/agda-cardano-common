{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `LiveHeavyFacts` — the DISCHARGE of `LiveNoDivH.Descent`'s six parameters,
-- i.e. the one module of the CSP-refinement route whose import closure sits on
-- the heavy `LTL/Walk/*` suffix.  Its export is the instantiated
--
--     noDivH : (r : RState) → ¬ Diverges (radec r ∖ hidden blkA)
--
-- (plus the whole `Descent` interface, re-exported `public`), which is exactly
-- (P4) of `LiveFSim.Sim` and the divergence-freedom premise of `LivenessProof`'s
-- unconditional corollary.
--
-- FIVE OF THE SIX PARAMETERS ARE DISCHARGED BY NAMING.  Each was re-derived at
-- source before use (module:line and verbatim type):
--
--   · `μTot`        `LTL/Walk/Walk.agda:139-140`
--                     μTot : SysState → ℕ
--                     μTot s = μG1 s + (μG2 s + breakBudget (med s))
--   · `μτ`          `LTL/Walk/WalkConvMeasure.agda:432-433`
--                     μτ : RState → ℕ ;  μτ r = μτ-sys (toSys r)
--   · `τreflect`    `LTL/Walk/WalkConvNoDiv.agda:138-139`
--                     (r : RState) {M} → radec r ─[ τ ]─► M
--                       → Σ[ r′ ] (M ≡ radec r′) × (μτ r′ < μτ r)
--   · `liftτ*-μ`    `LTL/Walk/WalkTauMu.agda:189-192`
--                     (r : RState) {u} → radec r ─[τ*]─► u
--                       → Σ[ r′ ] (u ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r))
--   · `liftReach-ev` `LTL/Walk/WalkStepLift.agda:79-81`
--                     (r : RState) {e} {t′} → radec r ═[ ev (evl e) ]═► t′
--                       → Σ[ r′ ] (t′ ≡ radec r′)
--
-- WHY `τreflect` AND `liftτ*-μ` RATHER THAN THE CHARTERED `τreflect-lex`.  The
-- merged per-τ reflector ("`μTot`-neutral AND `μτ`-strict at ONE successor") was
-- chartered as a ~40-line re-assembly of `WalkConvNoDiv.τreflect` and
-- `WalkTauMu.τreflect-μ`.  It is not.  The two agree on the `medτ` arm (both
-- invert with `WalkConvTauInv.medium-τ-inv-wt` and rebuild the SAME `m′`), but
-- the `hidSync` arm diverges in BOTH of its halves:
--   · the NODE half calls two DIFFERENT cones —
--     `WalkConvNodeDrop.top-nodes-io-abs-wt` (`:1263`, the `nodesWt` drop) and
--     `WalkConvNodeFix.top-nodes-io-abs-fix` (`:510`, the six driver equalities)
--     — each building its own successor `SysState` through its own 4×12 dispatch
--     and projecting the other's payload away (the fix cone re-uses
--     `absBundleG-io-prod-wt` and discards its `drop` field: the campaign's G2
--     wall verbatim);
--   · the MEDIUM half likewise calls two DIFFERENT inversions —
--     `WalkConvEvInv.medium-ev-inv-wt′` (`:424-427`, the `medWt m′ ≡ suc (medWt
--     m)` rise `μτ-io-dec` consumes) at `τreflect-io`, and `WalkTauMu`'s own
--     `medium-ev-inv-brk` (`:93-99`, the `breakBudget` fixity) at `τreflect-io-μ`
--     — so even the successor MEDIUM state is built twice.  (Reviewer's
--     strengthening of the finding: the wall is not confined to the node cones.)
-- `radec r₁ ≡ radec r₂` does not give `r₁ ≡ r₂` — no decode in this
-- development is injective — so the merge needs a THIRD, combined cone (~500
-- lines of re-mirror) and a combined medium inversion besides.  `LiveNoDivH`'s
-- descent was therefore ANCHORED instead
-- (see that module's header): the trace measure is read at the anchor config and
-- carried forward along the τ-RUN by `liftτ*-μ`, so no state-pairing is ever
-- required and both halves are consumed exactly as banked.
--
-- THE SIXTH, `hidEv-μ`, IS THE EVENT-CLASS SPLIT (§2) — the only new content
-- here.  Its clause heads MIRROR `LTL/Walk/WalkDeliver.agda:153-270`'s total
-- split of the `Net_Api` constructor set, which is what corroborates totality
-- mechanically rather than from prose.  Two differences, both simplifications:
-- this split takes a STRONG step (so the refutation clauses apply the per-state
-- refutations directly, with no `refute-weak` weak-lift), and `break` is REFUTED
-- from the hidden-membership premise instead of being a real case.
--
-- No postulates, holes, `--allow-unsolved-metas`, `NON_TERMINATING` or `mutual`.
-- Every imported module is READ-ONLY; one `import M blkA` per parameterised
-- module.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveHeavyFacts
  (blkA : Block₃) where

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥-elim )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ-syntax; _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Process_Trees using ( ExtI )

------------------------------------------------------------------------
-- The shared alphabet and the semantic vocabulary.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack ; store; env )
  renaming ( done to netDone )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( EventSet )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( ev; evl; evLabel; _─[_]─►_ )

------------------------------------------------------------------------
-- The reachable-config foundation and the two refutation families.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( aicCS; aicBF; aicDone )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( oevB-refute; oevB-no-io )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR

------------------------------------------------------------------------
-- THE HEAVY SUFFIX — the five banked lemmas, and the exposure cone the class
-- split is built from.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvMeasure blkA
  using ( μτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNoDiv blkA
  using ( τreflect )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkTauMu blkA
  using ( liftτ*-μ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkStepLift blkA
  using ( liftReach-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkReachExpose blkA
  using ( reach-ev-expose )

------------------------------------------------------------------------
-- The statement module (the hidden event set) and the descent engine.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( hidden )
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveNoDivH blkA
  as LNDH

------------------------------------------------------------------------
-- §2  `hidEv-μ` — ONE HIDDEN VISIBLE STEP DROPS `μTot`.
--
-- Total over the `Net_Api` constructor set, in the clause order of
-- `WalkDeliver.deliver` (`:153-270`).  Three kinds of clause:
--
--   · REAL (apiCS `:157`, apiBF `:164-203`, netDone `:209`) — the exposure cone
--     `WalkReachExpose.reach-ev-expose` (`:116-121`) gives the reachable
--     successor and the strict `μTot` drop; its `apiES .mem` side condition is
--     `tt` at every one of `deliver`'s ten call sites and is `tt` here too, and
--     its weak-move and `DReport` payloads are dropped.  `deliver` splits the
--     eight apiBF tags because its `Pr-step` analysis is tag-sensitive; nothing
--     here is, and `IsApiCSBF`'s `aicBF` is tag-generic (`SysOracle:1948`), so
--     the eight collapse to one clause.
--   · REFUTED-BY-PREMISE (`break`) — `keptB b (_ , break _) _ = true`
--     (`Spec.lagda.md:110`), so the hidden-membership premise is `true ≡ false`.
--     This is the ONE clause where `deliver` has a real body and this split has
--     none: a break is KEPT, hence never a `ModAStep` of `hidden blkA`.
--   · REFUTED-BY-STATE (apiKA/TS/LN/LF `:223-235`, input/output `:241-243`, and
--     the six wire classes `:247-267`) — no reachable abstract config offers
--     them at all.  `deliver` needs `refute-weak` to peel a weak move first;
--     this split is handed the STRONG step, so the per-state refutations
--     (`SysBisim.oevB-refute` / `oevB-no-io` over `SysRoute.medium-no-*` /
--     `absnodes-no-*`) apply directly.
------------------------------------------------------------------------

-- a hidden visible step from a reachable config lands on a reachable config
-- with a STRICTLY smaller trace measure
hidEv-μ : (r : RState) {B : Set 0ℓ} {e : Net_Api Payload B} {a : B} {M : NetProc}
    → EventSet.mem (hidden blkA) (B , e) a
    → radec r ─[ ev (evl (evLabel B e a)) ]─► M
    → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μTot (toSys r′) < μTot (toSys r))

-- apiCS (a driver's ChainSync api event)
hidEv-μ r {e = apiCS l₀ d₀ m} _ step with reach-ev-expose r aicCS tt step
... | r′ , eq , _ , lt , _ = r′ , eq , lt

-- apiBF, all eight tags at once (`aicBF` is tag-generic)
hidEv-μ r {e = apiBF l₀ d₀ m} _ step with reach-ev-expose r aicBF tt step
... | r′ , eq , _ , lt , _ = r′ , eq , lt

-- netDone (a driver receiving the CS server's api done callback)
hidEv-μ r {e = netDone l₀ d₀ id} _ step with reach-ev-expose r aicDone tt step
... | r′ , eq , _ , lt , _ = r′ , eq , lt

-- `break` is KEPT, so it is never hidden: the premise is `true ≡ false`
hidEv-μ r {e = break l₀} () step

-- the inert api classes: no reachable state offers them (medium and abstract
-- nodes both refuse; the nodes' refusal is the non-`IsApiCSBF` one)
hidEv-μ r {e = apiKA l₀ d₀ m} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiKA (med (toSys r)))
            (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
hidEv-μ r {e = apiTS l₀ d₀ m} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiTS (med (toSys r)))
            (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
hidEv-μ r {e = apiLN l₀ d₀ m} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLN (med (toSys r)))
            (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
hidEv-μ r {e = apiLF l₀ d₀ m} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLF (med (toSys r)))
            (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)

-- the io classes: `∖ ioES` makes them invisible at the top
hidEv-μ r {e = input l₀ d₀ id} _ step = ⊥-elim (oevB-no-io r tt step)
hidEv-μ r {e = output l₀ d₀ id} _ step = ⊥-elim (oevB-no-io r tt step)

-- the six wire classes: offered by neither the medium nor the abstract nodes
hidEv-μ r {e = sndmsg l₀ d₀ id} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndmsg (med (toSys r)))
            (SR.absnodes-no-sndmsg (toSys r)) step)
hidEv-μ r {e = rcvmsg l₀ d₀ id} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvmsg (med (toSys r)))
            (SR.absnodes-no-rcvmsg (toSys r)) step)
hidEv-μ r {e = tx l₀ d₀ id} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-tx (med (toSys r)))
            (SR.absnodes-no-tx (toSys r)) step)
hidEv-μ r {e = sndack l₀ d₀ id} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndack (med (toSys r)))
            (SR.absnodes-no-sndack (toSys r)) step)
hidEv-μ r {e = rcvack l₀ d₀ id} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvack (med (toSys r)))
            (SR.absnodes-no-rcvack (toSys r)) step)
hidEv-μ r {e = ack l₀ d₀ id} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-ack (med (toSys r)))
            (SR.absnodes-no-ack (toSys r)) step)
hidEv-μ r {e = store l₀ d₀ id} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-store (med (toSys r)))
            (SR.absnodes-no-store (toSys r)) step)
hidEv-μ r {e = env l₀ d₀ id} _ step =
  ⊥-elim (oevB-refute r (SR.medium-no-env (med (toSys r)))
            (SR.absnodes-no-env (toSys r)) step)

------------------------------------------------------------------------
-- §3  THE INSTANTIATION — `Descent` at the six discharges, re-exported whole.
-- Consumers get `noDivH` / `ndivH-init` / `ndivsReach` / `ndivs` by bare name.
------------------------------------------------------------------------

open LNDH.Descent μTot μτ τreflect liftτ*-μ hidEv-μ liftReach-ev public

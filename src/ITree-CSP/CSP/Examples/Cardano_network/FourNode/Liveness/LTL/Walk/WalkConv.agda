{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — τ-CONVERGENCE of `abstractSystem` (the WalkConv crux engine).
--
-- The R3 liveness walk (`Walk.agda`) must EXCLUDE the non-delivering
-- `WTrace` terminal `div : Diverges (radec r) → WTrace` (a silent infinite
-- τ-chain emits no visible event, so it can never satisfy `arrivedD`).
-- Excluding it needs, for every reachable abstract config `r`,
--
--     absNoDiv : (r : RState) → ¬ Diverges (radec r)
--
-- i.e. the abstract system τ-CONVERGES.  This was the ONE obligation R2 left
-- open on the divergence axis: R2's `odiv→`/`odiv←` were discharged by a
-- COINDUCTIVE transfer (`SysBisim.divChain`, guarded — NO measure), never by
-- refuting `Diverges`.  Refuting `Diverges` is the genuinely NEW content and
-- is INDUCTIVE (well-founded descent on a ℕ-measure), not coinductive.
--
-- STEP-0 GATE (verified from source, records the soundness of the approach):
-- the drivers `produce`/`consume`/`consume-k`
-- (`FourNode/FourNodeDiamond.lagda.md:196-239`) are FINITE linear `⟶`-chains
-- (produce = 9 api/done events then `Skip`; consume = 2 events then the
-- 4-event `consume-k` ending `Ret b′`; nodeB/C/D compose these finitely with
-- `>>=`/`>>` — there is NO infinite `iter` emitting blocks forever).  The
-- abstract nodes are `tableSpec` FSMs and are NATIVE-react τ-free
-- (`SysOracle_NodeTauEv.absNodesOf-no-τ`).  Hence `abstractSystem` is
-- τ-CONVERGENT (finitely many blocks ⇒ finitely many wire relays ⇒ finitely
-- many hidden τ's) and `¬ Diverges` is provable in principle — R3 needs NO
-- fairness (RISK-A FORCED verdict).
--
-- THE MEASURE (`μτ`) — the two abstract τ classes and how each decreases it.
-- By `SysStep.reflect-absDec-τ` every abstract τ of
-- `radec r = (decMed (med (toSys r)) ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES`
-- reflects to EXACTLY ONE of:
--   (i)  MEDIUM-τ  — `reflect-inner-τ … | medτ`: one cell drains
--        `draining x → empty` (`SysOracle_TauCore.medium-τ-inv` returns the
--        `flipCell`-updated `MedState`; the abstract nodes are UNCHANGED, the
--        `nodesτ` branch being VACUOUS by `absNodesOf-no-τ`).
--   (ii) io-SYNC   — `reflect-absDec-τ … | hidSync`: a hidden io event synced
--        between the medium (`medium-ev-inv`: one cell `empty → full x` on an
--        INPUT, or `full x → draining x` on an OUTPUT) and EXACTLY ONE abstract
--        node advancing one wire event (`SysIoLink6.top-nodes-io-abs` →
--        per-peer `nodeX-ev-io-abs`).
-- A measure that STRICTLY DECREASES on BOTH classes is
--     μτ  =  3 · (Σ over the abstract node FSMs of remaining wire events)
--         +  Σ over the medium cells of cellWt,   cellWt empty=0 full=1 draining=2.
-- Then: medium-τ drops a cell 2→0 (−2), nodes fixed ⇒ ↓.  io-sync OUTPUT
-- drops a node receive (−3) and a cell 1→2 (+1) ⇒ net −2 ⇒ ↓.  io-sync INPUT
-- drops a node send (−3) and a cell 0→1 (+1) ⇒ net −2 ⇒ ↓.  (The io-sync
-- summand is exactly R2's deferred summand (c): `SysStep.μ` header,
-- "the io-sync summand … is the remaining piece needed to make μ strictly
-- decrease across EVERY τ".)  The 3·(remaining wire events) component is the
-- driver-bounded block-flow work: finite because the drivers are finite.
--
-- THIS MODULE delivers the WELL-FOUNDED DESCENT ENGINE `absNoDiv`
-- PARAMETERISED over `μτ` and the per-τ strict-decrease reflector `τreflect`.
-- Instantiating `τreflect` is the remaining R3 crux (its io-sync node-side
-- per-peer wire-count decrease is the heavy `SysIoLink6`/`SysOracle` inversion
-- cone).  The engine itself is LIGHT (only `SysReach` + `Data.Nat` WF) and
-- 0-postulate, and turns any such measure into `absNoDiv`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConv (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

-- R2 reachable-config machinery: the reachable subtype `RState`, its abstract
-- decode `radec r = absDec (toSys r)`, and the whole-system process type.
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys )

-- labelled steps `─[ l ]─►` + the silent label `τ` + the coinductive
-- divergence predicate `Diverges` (an infinite τ-chain).
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; Diverges )

------------------------------------------------------------------------
-- THE WELL-FOUNDED τ-CONVERGENCE ENGINE.
--
-- Given
--   · a measure `μτ : RState → ℕ`, and
--   · `τreflect` : from ANY abstract τ-step `radec r ─[τ]─► M`, a reachable
--     target `r′` with `M ≡ radec r′` (so the abstract successor is again a
--     reachable config's decode) AND `μτ r′ < μτ r` (strict descent),
-- the abstract system cannot diverge from any reachable `r`.
--
-- `Diverges (radec r)` unfolds to a first τ-step `radec r ─[τ]─► next`
-- (`Diverges.step`) plus `Diverges (next)` (`Diverges.rest`).  `τreflect`
-- turns the step into a strictly smaller reachable `r′` with `next ≡ radec r′`;
-- transporting `rest` along that equality restarts the argument at `r′`.  An
-- infinite τ-chain would give an infinite `<`-descent of `μτ`, impossible by
-- `<`-well-foundedness — so the recursion (guarded by `Acc`) bottoms out and
-- `Diverges (radec r)` is refuted.
------------------------------------------------------------------------

module _ (μτ : RState → ℕ)
  (τreflect : (r : RState) {M : NetProc}
            → radec r ─[ τ ]─► M
            → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μτ r′ < μτ r))
  where

  -- accessible form: with `μτ r` accessible, no divergence from `r`
  absNoDiv-acc : (r : RState) → Acc _<_ (μτ r) → ¬ Diverges (radec r)
  absNoDiv-acc r (acc rec) d with τreflect r (d .Diverges.step)
  ... | r′ , M≡ , lt =
        absNoDiv-acc r′ (rec lt) (subst Diverges M≡ (d .Diverges.rest))

  -- τ-CONVERGENCE of the abstract system at every reachable config
  absNoDiv : (r : RState) → ¬ Diverges (radec r)
  absNoDiv r = absNoDiv-acc r (<-wellFounded (μτ r))

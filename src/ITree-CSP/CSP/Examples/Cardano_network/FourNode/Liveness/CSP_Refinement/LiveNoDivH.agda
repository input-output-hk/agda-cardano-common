{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `LiveNoDivH` — DIVERGENCE-FREEDOM of the hidden abstraction (design-doc
-- step 4 / Phase-1 Task 5): the `ndivL` obligation of the four-node
-- block-liveness failure simulation.
--
-- The CSP-refinement target (`CSP_Refinement.Spec.LivenessSpec`)
--     ∀ b → LSpec b true true ⊑FD (breakableSystemOf b ∖ hidden b)
-- is discharged through the τ-free abstraction `abstractSystem`
-- (`R2_Bisim.AbstractSystem`), and its `⊑D` half needs exactly one fact:
--
--     ndivs : ∀ {s} → ¬ divergences (abstractSystem ∖ hidden blkA) s
--
-- i.e. the HIDDEN abstraction never livelocks, at any trace prefix.
--
-- THE ROUTE (constructive; NO `MAcc` closure calculus, NO `¬DivModA→MAcc`).
-- `Hide-Diverges→ : Diverges (P ∖ A) → DivModA A P` (`CSP.Laws.FD.
-- HideDivergence:72-74`, itself literally `DRCongruence.div∖→modA`, which is
-- postulate-free) turns a divergence of the hidden system into an infinite
-- path of `abstractSystem` whose every step is a τ OR a HIDDEN visible event
-- (`ModAStep (hidden blkA)`).  That path is refuted by strict descent of an
-- ℕ-measure under ordinary well-founded `<` — no accessibility axiom.
--
-- THE MEASURE — a LEXICOGRAPHIC PAIR `(μTot , μτ)` under
-- `×-Lex _≡_ _<_ _<_`, taken at an ANCHOR/CURRENT pair of configs (see "THE
-- ANCHORED FORM" below), and the reason it must be a pair is NOT that any
-- visible class is measure-inert:
--
--   · a HIDDEN VISIBLE step strictly drops the trace measure `μTot`.  The
--     abstract system's whole visible alphabet is the closed 4-class
--     {apiCS, apiBF, netDone, break}; of those, `break` is KEPT and the other
--     three are the hidden ones, so the classes this measure has to descend on
--     are exactly {apiCS, apiBF, netDone} — see the `break` note below;
--   · a τ step is `μTot`-NEUTRAL (`liftτ*-μ` returns `≡`, not `<`) and
--     strictly drops the τ measure `μτ`.
--
-- So neither component alone descends on both classes, while the lex pair
-- descends on both — the first component on visible steps, the second on τ
-- steps with the first held fixed.  `break` is a KEPT event — `keptB b
-- (_ , break _) _ = true` (`CSP_Refinement/Spec.lagda.md:110`), so it is
-- excluded BY CONSTRUCTION, not by omission — hence never a `ModAStep` of
-- `hidden blkA`, so it needs NO descent obligation here at all; kept events
-- enter only through `ndivs`' trace-prefix closure, where mere REACHABILITY
-- (no measure) suffices.
--
-- THE ANCHORED FORM, and WHY (the Phase-2 correction to this module's own
-- design; the reason `τreflect-lex` is NOT a parameter).
-- The naive pair takes both components at the SAME config, which forces ONE τ
-- reflector to deliver a successor that is simultaneously `μTot`-neutral and
-- `μτ`-strict.  No such reflector exists and none is cheap to build: the two
-- banked halves (`WalkConvNoDiv.τreflect:138` for `μτ <`, `WalkTauMu.τreflect-μ
-- :166` for `μTot ≡`) agree on the `medτ` arm but, on the `hidSync` arm, call
-- TWO DIFFERENT node cones (`WalkConvNodeDrop.top-nodes-io-abs-wt:1263` vs
-- `WalkConvNodeFix.top-nodes-io-abs-fix:510`), each of which builds its own
-- successor `SysState` through its own 4×12 dispatch and PROJECTS AWAY the
-- other's payload (the fix cone literally re-uses `absBundleG-io-prod-wt` and
-- discards its `drop` field).  `radec r₁ ≡ radec r₂` does not give `r₁ ≡ r₂` —
-- no decode is injective anywhere in this development — so the two successors
-- cannot be reconciled without a third, merged cone (~500 lines).
-- The ANCHORED measure needs no merge.  `μA r rk = (μTot (toSys r) , μτ rk)`
-- takes the FIRST component at an ANCHOR config `r` — the config the last
-- visible step landed on — and the SECOND at the CURRENT config `rk`, and the
-- descent additionally carries the τ-run `radec r ─[τ*]─► radec rk` between
-- them.  A τ step then only has to move `rk` (`τreflect`, verbatim), the anchor
-- and hence the first component being untouched (`inj₂ (refl , …)`); and at a
-- hidden VISIBLE step the accumulated run is handed to `liftτ*-μ` (verbatim),
-- which returns SOME config `rj` with `radec rk ≡ radec rj` and `μTot (toSys rj)
-- ≡ μTot (toSys r)`.  The visible step is a statement about TREES, so it
-- transports along that equation — the pairing wall is bypassed by moving the
-- STEP to the measured config instead of moving the measure to the step's
-- config.  `hidEv-μ` at `rj` then re-anchors (`inj₁ …`).
--
-- MODULE-PARAMETER DISCIPLINE (the house pattern of `LTL/Walk/WalkConv`).
-- The banked μ-descent lemmas live in the HEAVY `LTL/Walk/*` suffix, whose
-- typecheck is minutes-scale.  This module therefore imports only the CHEAP
-- prefix (`AbstractSystem` / `SysDecode` / `SysStep` / `SysReach` + the
-- statement module `CSP_Refinement.Spec`) and takes the two measures and the
-- three step facts as parameters of the inner module `Descent` — exactly as
-- `WalkConv` parameterises its τ-convergence engine over `(μτ , τreflect)`
-- (a NAMED inner module rather than `WalkConv`'s anonymous one, so a consumer
-- writes `open LNDH.Descent μTot μτ τreflect liftτ*-μ hidEv-μ liftReach-ev`
-- ONCE and then uses `ndivs` &c. by bare name, instead of re-passing six
-- arguments to each export).  The parameters cannot sit in the OUTER telescope: their types
-- mention `RState`/`SysState`/`hidden`, which only exist once `blkA` is in
-- scope, i.e. only after the module header.
-- Phase 2's `LiveHeavyFacts` is the SOLE importer of `Walk*` and instantiates
-- them there.  Each parameter's comment names the banked lemma (module:line
-- and verbatim type, read off the real file) that discharges it.
--
-- WHAT THIS MODULE DOES *NOT* GIVE.  `ndivs` is divergence-freedom of the
-- ABSTRACT hidden system, which is exactly the `(∀ {s} → ¬ divergences Q s)`
-- premise of `Semantics.FDFromF.⊑F→⊑FD-df` at `Q := abstractSystem ∖ hidden
-- blkA`.  The statement's own right-hand side is the CONCRETE
-- `breakableSystemOf b ∖ hidden b`; carrying divergence-freedom across is the
-- separate `≈DR` transfer (`DeadlockDR.drbisim-divergenceFree` composed with
-- `cong-∖ … sysBisim`), and is Phase 2's job, not this module's.
--
-- No postulates, holes, `--allow-unsolved-metas`, `NON_TERMINATING`, or
-- `mutual` blocks.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveNoDivH
  (blkA : Block₃) where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (List)
open import Data.Product using (Σ-syntax; _,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Product.Relation.Binary.Lex.Strict using ( ×-Lex; ×-wellFounded )
open import Induction.WellFounded using ( Acc; acc; WellFounded )
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees using ( ExtI; deadlock )

------------------------------------------------------------------------
-- The shared alphabet.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

-- the CSP operator layer at this alphabet (ONE application of `CSP.Operators`)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( EventSet; _∖_ )

------------------------------------------------------------------------
-- The LTS / trace / FD vocabulary at this alphabet.
------------------------------------------------------------------------

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; Event√; evl; evLabel; ev; τ; _─[_]─►_; Diverges )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; _─[τ*]─►_; τ*-refl; τ*-step; τ*-trans )
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev )
open import Semantics.FailuresDivergences
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( divergences; IsDivergence )

------------------------------------------------------------------------
-- The two generic hiding facts this proof rests on.
--
--   · `Hide-Diverges→` — the CONSTRUCTIVE bridge from a divergence of `P ∖ A`
--     to an infinite modulo-`A` path of `P`.  It is DEFINITIONALLY
--     `DRCongruence.div∖→modA`, which is postulate-free.  The two König
--     postulates that live in the imported modules (`HideDivergence.
--     ¬DivModA→MAcc`, `DRCongruence.modA-transfer`) are therefore in this
--     module's import closure but appear in NONE of its proof terms — that is
--     the whole point of taking the descent route instead of the `MAcc` route;
--   · `Hide-τ-elim` / `Hide-ev-elim` — the single-step hide inversions, used
--     by the trace-prefix closure to walk `⟹⟨ s ⟩` of the hidden system.
------------------------------------------------------------------------

open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload})
  using ( ModAStep; maτ; maE; DivModA )
open DivModA using ( maNext; maStep; maRest )
open import CSP.Laws.FD.HideDivergence (Net_Api-≟ {Payload})
  using ( Hide-Diverges→ )
open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
  using ( HideτR; hτP; hτH; Hide-τ-elim
        ; HideevR; heV; he√; Hide-ev-elim )
open import CSP.Laws.Traces.TraceLawsParallelTrace (Net_Api-≟ {Payload})
  using ( deadlock-no-τ; deadlock-no-ev )

------------------------------------------------------------------------
-- The CHEAP prefix of the R2 development: the abstract endpoint, the config
-- state, and the reachable-config subtype with its decode and endpoint.
-- NONE of `SysBisim` / `SysOracle*` / `SysIoLink*` / `Walk*`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys; rinit; radec-init )

------------------------------------------------------------------------
-- The STATEMENT module: the hidden event set whose divergence-freedom is the
-- obligation (`hidden b .mem at a` is by definition `keptB b at a ≡ false`).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( hidden )

------------------------------------------------------------------------
-- THE LEXICOGRAPHIC ORDER on the measure pair (measure-independent, so it
-- lives outside the parameter block).
------------------------------------------------------------------------

-- strict lexicographic order on `ℕ × ℕ`: drop the first, or hold the first
-- and drop the second.  `inj₁ lt` is the visible-step case, `inj₂ (eq , lt)`
-- the τ-step case.
_≺_ : Rel (ℕ × ℕ) 0ℓ
_≺_ = ×-Lex _≡_ _<_ _<_

-- `_≺_` is well founded (both components are `<` on ℕ) — the ONE piece of
-- well-foundedness this module needs, straight from the standard library
≺-wellFounded : WellFounded _≺_
≺-wellFounded = ×-wellFounded <-wellFounded <-wellFounded

-- a trace of the whole system (the `Event√` list `divergences` is indexed by)
SysTrace : Set₁
SysTrace = List (Event√ (⊤ {0ℓ}))

------------------------------------------------------------------------
-- `deadlock` — the target of a `√` step — reaches nothing and diverges never.
------------------------------------------------------------------------

-- everything `⟹⟨ s ⟩`-reachable from `deadlock` is `deadlock`, which has no
-- τ at all; so no state reachable past a `√` can diverge.  This is what lets
-- the trace closure below IGNORE the question of whether the abstract system
-- can `ret` (design-doc §9(d)): a `√` step is not a dead end for the proof.
dlNoDiv : {s : SysTrace} {W : NetProc} → deadlock ⟹⟨ s ⟩ W → ¬ Diverges W
dlNoDiv ⟹-refl        d = deadlock-no-τ (d .Diverges.step)
dlNoDiv (⟹-τ  st _)   _ = ⊥-elim (deadlock-no-τ  st)
dlNoDiv (⟹-ev st _)   _ = ⊥-elim (deadlock-no-ev st)

------------------------------------------------------------------------
-- THE PARAMETER BLOCK — the two banked measures and the three banked step
-- facts.  Phase 2's `LivenessProof` supplies all five, then `open`s this
-- module so the four headline exports are available by bare name.
------------------------------------------------------------------------

module Descent
  -- the WHOLE-TRACE measure.  Instantiate with
  --   `LTL/Walk/Walk.agda:139`
  --     μTot : SysState → ℕ
  --     μTot s = μG1 s + (μG2 s + breakBudget (med s))
  (μTot : SysState → ℕ)

  -- the τ measure.  Instantiate with
  --   `LTL/Walk/WalkConvMeasure.agda:432`
  --     μτ : RState → ℕ
  (μτ : RState → ℕ)

  -- ONE τ STEP: a reachable successor with a STRICT `μτ` drop.  NO `μTot`
  -- payload is asked of it — that is what the anchoring buys (see "THE ANCHORED
  -- FORM" in the header; the merged both-payloads reflector does not exist and
  -- is not cheap).  Instantiate VERBATIM with
  --   `LTL/Walk/WalkConvNoDiv.agda:138`
  --     τreflect : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  --       → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μτ r′ < μτ r)
  (τreflect : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
      → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μτ r′ < μτ r))

  -- A WHOLE τ-RUN: a reachable endpoint with the SAME `μTot` (every abstract τ
  -- is `μTot`-neutral — the medium drain keeps nodes and `broken` literal, an
  -- io-sync keeps the break budget and the six group drivers).  This is what
  -- carries the anchor's trace measure forward to the config where the hidden
  -- visible step fires.  Instantiate VERBATIM with
  --   `LTL/Walk/WalkTauMu.agda:189`
  --     liftτ*-μ : (r : RState) {u : NetProc} → radec r ─[τ*]─► u
  --       → Σ[ r′ ∈ RState ] (u ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r))
  (liftτ*-μ : (r : RState) {u : NetProc} → radec r ─[τ*]─► u
      → Σ[ r′ ∈ RState ] (u ≡ radec r′) × (μTot (toSys r′) ≡ μTot (toSys r)))

  -- ONE HIDDEN VISIBLE STEP: a reachable successor with a STRICT `μTot` drop.
  -- Stated over CHEAP vocabulary (`hidden`/`keptB` from the statement module)
  -- because the banked lemma's own side conditions are HEAVY-module
  -- predicates (`IsApiCSBF`, `DReport` — `R2_Bisim/SysRoute`, `SysOracle`)
  -- that this module may not even mention.  Discharge in Phase 2 by splitting
  -- the event class:
  --   · apiCS / apiBF / netDone — `LTL/Walk/WalkReachExpose.agda:116`
  --       reach-ev-expose : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X}
  --           {a : X} {M : NetProc}
  --         → IsApiCSBF e → apiES .mem (X , e) a
  --         → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  --         → Σ[ r′ ∈ RState ] (M ≡ radec r′)
  --             × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
  --             × (μTot (toSys r′) < μTot (toSys r)) × DReport (toSys r) (toSys r′) e a
  --     (its weak-move wrapper `liftReach-ev-expose`, `:152`, also serves — pad
  --     the strong step with `wev τ*-refl _ τ*-refl`, as `ndivsReach` does below);
  --   · apiKA / apiTS / apiLN / apiLF, io, and every wire class — REFUTED at
  --     every reachable config (`SysBisim.oevB-refute` / `oevB-no-io`,
  --     `SysRoute.medium-no-*` / `absnodes-no-*`);
  --   · `break` — EXCLUDED by the premise: `keptB blkA (_ , break l) a ≡ true`
  --     (`CSP_Refinement/Spec.lagda.md:110`), so a break is never hidden.
  --
  -- THE PRECEDENT THAT MAKES THIS CHEAP — DO NOT RE-DERIVE THE CLASS SPLIT.
  -- `LTL/Walk/WalkDeliver.agda`'s `deliver` (`:153-270`) already performs this
  -- exact split, TOTALLY and typechecked, over the whole `Net_Api` constructor
  -- set: real bodies for apiCS (`:157`), the eight apiBF tags (`:164`-`:203`),
  -- netDone (`:209`) and break (`:216`); refutation bodies for apiKA/TS/LN/LF
  -- (`:223`,`:227`,`:231`,`:235`), input/output (`:241`,`:243`) and all six wire
  -- classes (`:247`-`:267`).  So the closed 4-class visible alphabet is
  -- MECHANICALLY corroborated, not merely read off prose.  Better still, all ten
  -- of its `liftReach-ev-expose` call sites discharge the `apiES .mem` side
  -- condition as literally `tt` (`:158`,`:165`,`:173`,`:178`,`:183`,`:188`,
  -- `:193`,`:198`,`:203`,`:210`), so that premise costs nothing.  Phase 2 should
  -- MIRROR those clause heads; only the `break` clause changes (there it is a
  -- real case, here the premise kills it).
  (hidEv-μ : (r : RState) {B : Set 0ℓ} {e : Net_Api Payload B} {a : B} {M : NetProc}
      → EventSet.mem (hidden blkA) (B , e) a
      → radec r ─[ ev (evl (evLabel B e a)) ]─► M
      → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (μTot (toSys r′) < μTot (toSys r)))

  -- ONE KEPT VISIBLE MOVE: a reachable successor, NO measure needed (the
  -- trace-prefix closure of `ndivs` only has to stay inside the reachable
  -- set).  Instantiate VERBATIM with
  --   `LTL/Walk/WalkStepLift.agda:79`
  --     liftReach-ev : (r : RState) {e : Event} {t′ : NetProc}
  --       → radec r ═[ ev (evl e) ]═► t′ → Σ[ r′ ∈ RState ] (t′ ≡ radec r′)
  -- It is UNCONDITIONAL (no event-class side condition), so it covers the
  -- breaks and both `blkA` api classes at once — no separate
  -- `liftReach-break-*` parameter is needed.
  (liftReach-ev : (r : RState) {e : Event} {t′ : NetProc}
      → radec r ═[ ev (evl e) ]═► t′
      → Σ[ r′ ∈ RState ] (t′ ≡ radec r′))
  where

  ----------------------------------------------------------------------
  -- THE MEASURE and the per-`ModAStep` strict descent.
  ----------------------------------------------------------------------

  -- the ANCHORED lexicographic measure: the TRACE measure of the anchor config
  -- `r` (the config the last visible step landed on) paired with the τ measure
  -- of the CURRENT config `rk`
  μA : RState → RState → ℕ × ℕ
  μA r rk = μTot (toSys r) , μτ rk

  ----------------------------------------------------------------------
  -- THE WELL-FOUNDED DESCENT: no infinite modulo-`hidden` path.
  ----------------------------------------------------------------------

  -- Accessible form.  Three coordinates travel together: the ANCHOR `r`, the
  -- CURRENT config `rk`, and the τ-run from the one to the other.  The two
  -- `ModAStep` constructors are exactly the two lex cases:
  --   · `maτ` — `τreflect` moves `rk` only; the anchor and hence the first
  --     component are untouched, so the descent is `inj₂ (refl , μτ-drop)`, and
  --     the fired τ is appended to the run;
  --   · `maE` — `liftτ*-μ` cashes the run in for a config `rj` that decodes to
  --     the same tree as `rk` and carries the ANCHOR's `μTot`; the visible step
  --     transports onto `rj` (it speaks of trees, not of configs), `hidEv-μ`
  --     drops `μTot` strictly there, and the successor becomes the NEW anchor
  --     with an empty run — `inj₁`.
  noDivModA-acc : (r rk : RState) → radec r ─[τ*]─► radec rk
                → Acc _≺_ (μA r rk)
                → ¬ DivModA (hidden blkA) (radec rk)
  noDivModA-acc r rk run (acc rec) dm with dm .maStep
  ... | maτ st with τreflect rk st
  ...   | rk′ , eq , ltτ =
          noDivModA-acc r rk′
            (τ*-trans run
              (τ*-step (subst (λ z → radec rk ─[ τ ]─► z) eq st) τ*-refl))
            (rec (inj₂ (refl , ltτ)))
            (subst (DivModA (hidden blkA)) eq (dm .maRest))
  noDivModA-acc r rk run (acc rec) dm | maE {B} {e} {a} hm st with liftτ*-μ r run
  ...   | rj , eqj , μeq
        with hidEv-μ rj hm
               (subst (λ z → z ─[ ev (evl (evLabel B e a)) ]─► dm .maNext) eqj st)
  ...     | r″ , eq″ , lt =
            noDivModA-acc r″ r″ τ*-refl
              (rec (inj₁ (subst (λ n → μTot (toSys r″) < n) μeq lt)))
              (subst (DivModA (hidden blkA)) eq″ (dm .maRest))

  -- HEADLINE 1: `abstractSystem` has no infinite (τ ∪ hidden-event) path from
  -- any reachable config (the config is its own anchor, with the empty run)
  noDivModA : (r : RState) → ¬ DivModA (hidden blkA) (radec r)
  noDivModA r = noDivModA-acc r r τ*-refl (≺-wellFounded (μA r r))

  ----------------------------------------------------------------------
  -- THE HIDE BRIDGE and the trace-prefix closure.
  ----------------------------------------------------------------------

  -- HEADLINE 2: the hidden abstraction cannot diverge at any reachable config
  noDivH : (r : RState) → ¬ Diverges (radec r ∖ hidden blkA)
  noDivH r d = noDivModA r (Hide-Diverges→ (hidden blkA) (radec r) d)

  -- HEADLINE 3: … in particular at the initial config, where the abstract
  -- decode IS `abstractSystem` (`SysReach.radec-init`)
  ndivH-init : ¬ Diverges (abstractSystem ∖ hidden blkA)
  ndivH-init = subst (λ z → ¬ Diverges (z ∖ hidden blkA)) radec-init (noDivH rinit)

  -- TRACE-PREFIX CLOSURE.  Generalised over the START tree with a
  -- `start ≡ radec r ∖ hidden blkA` witness so the `⟹⟨ s ⟩` sub-derivation is
  -- passed to the recursive call STRUCTURALLY UNCHANGED (the `subst` lands on
  -- the head STEP, never on the recursion argument) — the `WalkStepLift.liftτ*′`
  -- idiom that makes the descent pass the termination checker.
  --
  -- Three step classes, by the hide inversions:
  --   · a τ of the hidden system is a τ of `abstractSystem` (`hτP`) or a
  --     hidden event of it (`hτH`) — reachability from `τreflect` /
  --     `hidEv-μ` (their measures are discarded here);
  --   · a KEPT visible event (`heV`) — reachability from `liftReach-ev`;
  --   · a `√` (`he√`) — lands on `deadlock`, handled by `dlNoDiv`, so NO
  --     "the abstract system never rets" obligation arises.
  ndivsReach : (r : RState) {start : NetProc} → start ≡ radec r ∖ hidden blkA
             → {s : SysTrace} {W : NetProc} → start ⟹⟨ s ⟩ W → ¬ Diverges W
  ndivsReach r eq ⟹-refl = subst (λ z → ¬ Diverges z) (sym eq) (noDivH r)
  ndivsReach r eq (⟹-τ {q = M} st rest)
      with Hide-τ-elim (hidden blkA) (radec r) (subst (λ z → z ─[ τ ]─► M) eq st)
  ... | hτP P′ Pτ Meq with τreflect r Pτ
  ...   | r′ , eqr , _ =
          ndivsReach r′ (trans Meq (cong (_∖ hidden blkA) eqr)) rest
  ndivsReach r eq (⟹-τ {q = M} st rest)
      | hτH P′ hm Pev Meq with hidEv-μ r hm Pev
  ...   | r′ , eqr , _ =
          ndivsReach r′ (trans Meq (cong (_∖ hidden blkA) eqr)) rest
  ndivsReach r eq (⟹-ev {q = M} {e = e} st rest)
      with Hide-ev-elim (hidden blkA) (radec r) (subst (λ z → z ─[ ev e ]─► M) eq st)
  ... | he√ _ = dlNoDiv rest
  ... | heV P′ _ Pev with liftReach-ev r (wev τ*-refl Pev τ*-refl)
  ...   | r′ , eqr = ndivsReach r′ (cong (_∖ hidden blkA) eqr) rest

  -- HEADLINE 4 (the `ndivL` obligation): the hidden abstraction has NO
  -- divergence at ANY trace, i.e. `divergences (abstractSystem ∖ hidden blkA)`
  -- is empty.  Unfolding `IsDivergence`: a divergence is a `⟹⟨ prefix ⟩`-reach
  -- of some `witness` plus `Diverges witness`; the closure refutes exactly that.
  ndivs : {s : SysTrace} → ¬ divergences (abstractSystem ∖ hidden blkA) s
  ndivs d = ndivsReach rinit (cong (_∖ hidden blkA) (sym radec-init))
                       (d .IsDivergence.reach) (d .IsDivergence.divwit)

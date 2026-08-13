{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 Task 5 (FINAL assembly) — `sysBisim` (`Praos.SysBisim`).
--
-- GOAL:  sysBisim : systemBroken ≈DR abstractSystem
--   (`systemBroken = ⟦ initial ⟧` from `Praos.SysDecode`; `abstractSystem` from
--    `Praos.AbstractSystem`).  Assembled from the GENERIC (operand-polymorphic)
--    reflection/step machinery of `Praos.SysStep`.
--
-- ==================== SCOPE-FIRST PROBE (this increment) ================
-- Before grinding all cases, the two route-2 assembly RISKS are de-risked on
-- REPRESENTATIVE, TOTAL, hole-free code:
--
--   RISK 1 — TRACTABILITY / WHNF.  The concrete dispatcher applies the generic
--     `SysStep` lemmas to the REAL `⟦ s ⟧` / `decMed (med s)` / `nodesOf s`
--     operands.  `probe-*` below apply the generic top-level reflections
--     (`reflect-⟦⟧-τ`, `reflect-inner-τ`, `reflect-top-ev`, `reflect-absDec-τ`)
--     at those REAL operands by OPAQUE application (the operands are passed as
--     arguments, never `with`-forced to WHNF at our site).  Their typecheck
--     time is the tractability verdict (see the report).
--
--   RISK 2 — PRODUCTIVITY (`--guardedness`).  `sysBisim` is COINDUCTIVE; the
--     residual of each `.fwd`/`.bwd` field is a recursive bisim at the target
--     state, which must sit syntactically UNDER the record/tuple constructor
--     (guarded corecursion).  `buildDR`/`buildDRˢ` below are the guarded
--     copattern builder — the exact `mkDR`/`mkDRˢ` shape used in
--     `BlockFetchRefinement.BlockFetchNetRefinementBisim` — over a functional
--     relation, WITH the recursive call routed through a `subst` transport in
--     argument position (the known guardedness trap).  It typechecks under
--     plain `--guardedness`, so the pattern is productive (see the report).
--
-- The `dec-init` / `absDec-init` rewrites that turn the eventual whole-`SysState`
-- bisim `bisim′ initial` into `sysBisim` are wired here as `syswire` (a total
-- transport skeleton), leaving the whole-`SysState` `bisim′` itself — the total
-- per-leaf step dispatcher — as the remaining work (report: it is the large
-- finite enumeration, BlockFetchNetRefinementBisim-scale, ×4 protocols).
--
-- No postulates, holes, or `--allow-unsolved-metas`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Process_Trees using (PTree; ExtI; ret)
open PTree using (force)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim (blkA : Block₃) where

------------------------------------------------------------------------
-- The concrete model, the two endpoints, and the shared alphabet.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import Data.Unit using () renaming (⊤ to ⊤₀)
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

-- Net_Api operators (the whole-system alphabet), to state the inner-step probe
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; EventSet; viewV )
-- the Hide-hidden law (an io ∈ ioES fire becomes a τ through `∖ ioES`), for the
-- backward io-sync WEAK-τ lift; `Hide-ev-elim`/`heV` for `oevB`'s io refutation
-- (SysStep imports these non-`public`, so import direct)
open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
  using ( Hide-hidden; Hide-ev-elim; HideevR )
open HideevR using ( heV )
-- `noOffer→viewV` (the `¬ IoOffers → viewV ≡ nothing` bridge for the solo lift)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA as GB
open EventSet using ( mem )

-- the four concrete node decodes (the operands of `nodesOf`, for the nodesτ peel)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN

-- the whole-system process type (shared with `⟦_⟧` / `absDec` / the endpoints)
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the R1 concrete decode + its home equality (`⟦ initial ⟧ ≡ systemBroken`)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧; initial; dec-init )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBroken
  using ( systemBroken )
-- the R2 abstract target + its home equality (`absDec initial ≡ abstractSystem`)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )

-- the shared medium decode (the left operand of `⟦_⟧` / `absDec`)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed )
-- the whole generic step/reflection machinery (R2 Task 4)
-- qualified alias too, for the `TopEvR` constructors (`medEv`/`nodesEv` clash
-- with `comove-io-sync`'s argument names if opened unqualified)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep
  using ( absDec; absDec-init; nodesOf; absNodesOf
        ; absNodeA; absNodeB; absNodeC; absNodeD
        ; ReflOut; innerτ; hidSync; reflect-⟦⟧-τ; reflect-absDec-τ
        ; InnerτR; medτ; nodesτ; reflect-inner-τ
        ; NodesτR; nAτ; nBτ; nCτ; nDτ; reflect-nodes-τ
        ; TopEvR; reflect-top-ev
        ; ∖-τ; ∖-ev
        ; IoOffers; μ
        -- the operand-generic whole-system step-intro seals (the reflect-half's
        -- assembly of a concrete `⟦ s ⟧`/`absDec s` step from a leaf step)
        ; lift-nodes-whole-τ; lift-med-whole-τ; lift-io-sync-whole-τ
        ; lift-nodes-whole-ev; lift-med-whole-ev )
-- the R2 D1 reachable-config foundation (RState subtype + decoded transition
-- `_↝_` + reachable closure `rclose`) — the domain the compositional bisim walks
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; toSys; rdec; radec; rinit; rclose; rclose-abs
        ; rcloseʷ; rcloseʷ-abs
        ; _↝_; mkStep; Reachable; rStep; reach; mkR )
-- the R2 D3 top-level co-moves + impossible-event refutations (visible classes)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
-- the api-class witness constructors (`IsApiCSBF`), for the `oev` api dispatch
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA as SO
-- the R2 D3 io leaf machinery (`top-nodes-io` for `otau`'s hidSync branch)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink3 blkA as SIL
-- the R2 D3 abstract node-τ collapse (`nodeX-τ-inv-abs` for `otau`'s nodesτ branch)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink4 blkA as SIL4
-- the abstract nodes-τ VACUITY (`absNodesOf-no-τ` for `otauB`'s nodesτ branch)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA as SNT
-- the R2 D3 backward abstract node peels (`top-nodes-abs`/`top-nodes-io-abs` — the
-- abstract-primary → concrete-nodes weak run — for the backward `oevB`/`otauB` fields)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA as SIL6
-- the io / event alphabet constructors (for the `oev` label dispatch)
open import CSP.Examples.Cardano_network.Net p
  using ( apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; Link
        ; break; done; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )

-- the LTS + weak-bisim vocabulary
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; τ; evl; evLabel; Event; Event√; √; Diverges; sRet )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF )
open WSimF
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( DRbisim; _≈DR_; drbisim-refl )
open DRbisim
open import Process_Trees using ( deadlock )
-- the R2 D3 √ ret-transfer leaf machinery (`sys-ret-transfer` for `osqrt`;
-- `nodes-wret` + generic ret/τ* helpers for the backward `osqrtB`)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysSqrt blkA as SS
  using ( sys-ret-transfer; nodes-wret
        ; fHide-ret; fHide-ret-inv; ∥⇙-ret-inv; ∥⇙-ret-intro; ∥⇘⇙-τ*-R )
-- the R2 D3 forward-divergence measure `μ'Sys` + the μ'-aware nodes-τ drop
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDiv blkA as SD
  using ( μ'Sys; nodes-τ-μ'↓ )
open import Data.Nat using ( _<_ )
open import Data.Nat.Induction using ( <-wellFounded )
open import Induction.WellFounded using ( Acc; acc )

------------------------------------------------------------------------
-- RISK 1 PROBE — apply the generic reflections at the REAL system operands.
--
-- Each `probe-*` instantiates a generic (operand-polymorphic) `SysStep` lemma
-- at the REAL `⟦ s ⟧` / `decMed (med s)` / `nodesOf s` / `absNodesOf s`
-- operands, purely by application: the operands are handed over as arguments,
-- never `with`-forced to WHNF at this site.  Their (fast) typecheck is the
-- tractability verdict — the concrete dispatcher composes exactly these.
------------------------------------------------------------------------

-- reflect a hidden-τ of the REAL concrete `⟦ s ⟧` (opaque application)
probe-⟦⟧-τ : (s : SysState) {M″ : NetProc}
  → ⟦ s ⟧ ─[ τ ]─► M″ → ReflOut (decMed (med s)) (nodesOf s) M″
probe-⟦⟧-τ s step = reflect-⟦⟧-τ s step

-- split an inner `∥⇘ ioES ⇙` τ into the medium-vs-nodes cases at the REAL
-- operands (the branch `reflect-⟦⟧-τ`'s `innerτ` case hands to the dispatcher)
probe-inner-τ : (s : SysState) {P′ : NetProc}
  → (decMed (med s) ∥⇘ ioES ⇙ nodesOf s) ─[ τ ]─► P′
  → InnerτR (decMed (med s)) (nodesOf s) P′
probe-inner-τ s step = reflect-inner-τ (decMed (med s)) (nodesOf s) step

-- reflect a hidden-τ of the REAL abstract `absDec s` (opaque application at the
-- abstract operands) — the `.bwd .on-tau` seam
probe-absDec-τ : (s : SysState) {N : NetProc}
  → absDec s ─[ τ ]─► N → ReflOut (decMed (med s)) (absNodesOf s) N
probe-absDec-τ s step = reflect-absDec-τ s step

-- invert a visible non-io event of the REAL `⟦ s ⟧` given the disjointness
-- witness the dispatcher supplies (opaque application; medium-vs-nodes split)
probe-top-ev : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
               {M″ : NetProc}
  → (¬ IoOffers (decMed (med s)) e a) ⊎ (¬ IoOffers (nodesOf s) e a)
  → ⟦ s ⟧ ─[ ev (evl (evLabel X e a)) ]─► M″
  → TopEvR (decMed (med s)) (nodesOf s) e a M″
probe-top-ev s disj step = reflect-top-ev (decMed (med s)) (nodesOf s) disj step

------------------------------------------------------------------------
-- RISK 2 PROBE — the guarded coinductive builder (productivity).
--
-- `buildDR`/`buildDRˢ` are the `mkDR`/`mkDRˢ` guarded copattern builders over a
-- functional relation `EqR`.  They exercise EXACTLY the productivity-critical
-- shape of `sysBisim`: a coinductive `DRbisim` whose `.fwd`/`.bwd`/`.on-ev`/
-- `.on-tau` residuals are recursive `buildDR`/`buildDRˢ` calls sitting UNDER
-- the `_,_` (Σ) constructor, WITH the recursive argument routed through a
-- `subst` transport (the trap that breaks `--guardedness` when a recursive
-- call is helper-routed instead of constructor-guarded).  Typechecking under
-- plain `--guardedness` is the productivity verdict.
------------------------------------------------------------------------

-- the functional relation: two whole-system trees related when propositionally
-- equal (the transport-carrying analogue of `R = {(⟦ s ⟧, absDec s)}`)
data EqR : NetProc → NetProc → Set₁ where
  mkEqR : {W S : NetProc} → W ≡ S → EqR W S

-- transport an `EqR` witness along an equality of its left endpoint — the
-- `subst` the guarded builder threads through the recursive-call argument
transEqR : {W W′ S : NetProc} → W ≡ W′ → EqR W S → EqR W′ S
transEqR eq r = subst (λ z → EqR z _) eq r

-- the guarded builders (mutually corecursive; mkDRˢ = swapped orientation)
buildDR  : {W S : NetProc} → EqR W S → DRbisim (⊤ {0ℓ}) W S
buildDRˢ : {W S : NetProc} → EqR W S → DRbisim (⊤ {0ℓ}) S W
-- forward: the recursive residual is `buildDR (transEqR refl …)` UNDER `_,_`
buildDR (mkEqR refl) .fwd .on-ev  step =
  _ , wev τ*-refl step τ*-refl , buildDR  (transEqR refl (mkEqR refl))
buildDR (mkEqR refl) .fwd .on-tau step =
  _ , wτ (τ*-step step τ*-refl) , buildDR  (transEqR refl (mkEqR refl))
buildDR (mkEqR refl) .bwd .on-ev  step =
  _ , wev τ*-refl step τ*-refl , buildDRˢ (transEqR refl (mkEqR refl))
buildDR (mkEqR refl) .bwd .on-tau step =
  _ , wτ (τ*-step step τ*-refl) , buildDRˢ (transEqR refl (mkEqR refl))
buildDR (mkEqR refl) .div→ d = d
buildDR (mkEqR refl) .div← d = d
-- swapped orientation (same relation is symmetric under `refl`)
buildDRˢ (mkEqR refl) .fwd .on-ev  step =
  _ , wev τ*-refl step τ*-refl , buildDRˢ (transEqR refl (mkEqR refl))
buildDRˢ (mkEqR refl) .fwd .on-tau step =
  _ , wτ (τ*-step step τ*-refl) , buildDRˢ (transEqR refl (mkEqR refl))
buildDRˢ (mkEqR refl) .bwd .on-ev  step =
  _ , wev τ*-refl step τ*-refl , buildDR  (transEqR refl (mkEqR refl))
buildDRˢ (mkEqR refl) .bwd .on-tau step =
  _ , wτ (τ*-step step τ*-refl) , buildDR  (transEqR refl (mkEqR refl))
buildDRˢ (mkEqR refl) .div→ d = d
buildDRˢ (mkEqR refl) .div← d = d

------------------------------------------------------------------------
-- FINAL-REWRITE WIRING — the `dec-init`/`absDec-init` transport skeleton.
--
-- Once the whole-`SysState` bisim `bisim′ : (s : SysState) → ⟦ s ⟧ ≈DR absDec s`
-- is built (the remaining total per-leaf dispatcher — see the report), the
-- headline `sysBisim` follows by rewriting `bisim′ initial` with the two home
-- equalities.  `syswire` packages that final transport, so Task 5's closing
-- step is a single `syswire (bisim′ initial)`.
------------------------------------------------------------------------

-- given the whole-system bisim at `initial`, transport it to the endpoints via
-- `dec-init : ⟦ initial ⟧ ≡ systemBroken` and `absDec-init : absDec initial ≡
-- abstractSystem` — the final `sysBisim` assembly, modulo `bisim′ initial`
syswire : ⟦ initial ⟧ ≈DR absDec initial → systemBroken blkA ≈DR abstractSystem
syswire b =
  subst (λ z → z ≈DR abstractSystem) dec-init
    (subst (λ z → ⟦ initial ⟧ ≈DR z) absDec-init b)

------------------------------------------------------------------------
-- R2 D2 — the COMPOSITIONAL coinductive bisim `bisim′` over the reachable
-- subtype `RState`, parametric in a `StepOracle`.
--
-- WHY PARAMETRIC.  Each of the four `DRbisim` fields (`.fwd/.bwd × .on-ev/
-- .on-tau`) is a TOTAL obligation over an ARBITRARY LTS step of `rdec r` /
-- `radec r` (whose head `⟦ toSys r ⟧` is a stuck neutral for a variable `r`, so
-- the step cannot be case-analysed to representatives — Agda coverage forbids a
-- representative-only field, and the residual `DRbisim ⊤ M t₂′` is typed at the
-- ACTUAL target `M`, forcing a per-leaf `s′`-inversion `M ≡ rdec r′`).  The
-- reflect-half — "map each step to its reachable successor + the matching weak
-- move on the other decode" — is therefore the per-transition-class GRIND (D3),
-- ~30–60 classes.  `StepOracle` is exactly that interface; GIVEN it, `bisim′`
-- is a TOTAL, GUARDED coinductive walker (this module, hole-free).  This cleanly
-- separates the achievable D2 skeleton (the walker + the reachable packaging)
-- from the D3 leaf enumeration (populating the oracle).
------------------------------------------------------------------------

-- the per-transition-class REFLECT interface (the D3 grind target).  For each
-- reachable config `r`: each CONCRETE step of `rdec r` lands on some reachable
-- `r′` with the ABSTRACT side matching by a weak move (`otau`/`oev`); dually for
-- the ABSTRACT steps (`otauB`/`oevB`); and the two divergence transfers
-- (`odiv→`/`odiv←`, via `μ`).  The `M ≡ rdec r′` field is the leaf `s′`-inversion.
record StepOracle : Set₁ where
  field
    otau  : (r : RState) {M : NetProc} → rdec r ─[ τ ]─► M
          → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ τ ]═► radec r′))
    -- visible (non-√) forward class: the target is a `rdec r′` Hide-tree
    oev   : (r : RState) {e : Event} {M : NetProc} → rdec r ─[ ev (evl e) ]─► M
          → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ ev (evl e) ]═► radec r′))
    -- √ (terminal) forward class: a √ step targets `deadlock` (NOT any `rdec r′`),
    -- so its output is the raw WSimF triple with the terminal residual bisim
    -- (`drbisim-refl deadlock`).  This is the sound √ CO-MOVE enabled by the
    -- STEP-5 symmetrization (both 12-peer sides ret exactly at all-stDone).
    osqrt : (r : RState) {x : ⊤ {0ℓ}} {M : NetProc} → rdec r ─[ ev (√ x) ]─► M
          → Σ[ t′ ∈ NetProc ] ((radec r ═[ ev (√ x) ]═► t′) × DRbisim (⊤ {0ℓ}) M t′)
    otauB : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
          → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ τ ]═► rdec r′))
    -- visible (non-√) backward class + √ backward CO-MOVE (mirror of oev/osqrt)
    oevB  : (r : RState) {e : Event} {M : NetProc} → radec r ─[ ev (evl e) ]─► M
          → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ ev (evl e) ]═► rdec r′))
    osqrtB : (r : RState) {x : ⊤ {0ℓ}} {M : NetProc} → radec r ─[ ev (√ x) ]─► M
          → Σ[ t′ ∈ NetProc ] ((rdec r ═[ ev (√ x) ]═► t′) × DRbisim (⊤ {0ℓ}) M t′)
    odiv→ : (r : RState) → Diverges (rdec r) → Diverges (radec r)
    odiv← : (r : RState) → Diverges (radec r) → Diverges (rdec r)
open StepOracle public

-- the guarded coinductive walker (mutually corecursive with its swapped
-- orientation `bisim′ˢ-from`, exactly the `buildDR`/`buildDRˢ` shape).  Every
-- `.fwd/.bwd .on-ev/.on-tau` residual is a recursive walker call sitting
-- syntactically UNDER the `_,_` (Σ) constructor; the `M ≡ rdec r′` witness is
-- matched to `refl` (rewriting the step target to `rdec r′`), so NO `subst`
-- wraps the corecursive call — cleanly productive under plain `--guardedness`.
bisim′-from  : StepOracle → (r : RState) → DRbisim (⊤ {0ℓ}) (rdec r) (radec r)
bisim′ˢ-from : StepOracle → (r : RState) → DRbisim (⊤ {0ℓ}) (radec r) (rdec r)
-- forward: concrete steps reflected via `otau`/`oev`, residual = walker at `r′`
bisim′-from o r .fwd .on-tau step with o .otau r step
... | r′ , refl , wm = radec r′ , wm , bisim′-from o r′
bisim′-from o r .fwd .on-ev {l = evl e} step with o .oev r step
... | r′ , refl , wm = radec r′ , wm , bisim′-from o r′
bisim′-from o r .fwd .on-ev {l = √ x}  step = o .osqrt r step
-- backward: abstract steps reflected via `otauB`/`oevB`, residual = SWAPPED walker
bisim′-from o r .bwd .on-tau step with o .otauB r step
... | r′ , refl , wm = rdec r′ , wm , bisim′ˢ-from o r′
bisim′-from o r .bwd .on-ev {l = evl e} step with o .oevB r step
... | r′ , refl , wm = rdec r′ , wm , bisim′ˢ-from o r′
bisim′-from o r .bwd .on-ev {l = √ x}  step = o .osqrtB r step
bisim′-from o r .div→ d = o .odiv→ r d
bisim′-from o r .div← d = o .odiv← r d
-- swapped orientation (abstract on the left): mirrors the above with the
-- concrete/abstract oracle components exchanged
bisim′ˢ-from o r .fwd .on-tau step with o .otauB r step
... | r′ , refl , wm = rdec r′ , wm , bisim′ˢ-from o r′
bisim′ˢ-from o r .fwd .on-ev {l = evl e} step with o .oevB r step
... | r′ , refl , wm = rdec r′ , wm , bisim′ˢ-from o r′
bisim′ˢ-from o r .fwd .on-ev {l = √ x}  step = o .osqrtB r step
bisim′ˢ-from o r .bwd .on-tau step with o .otau r step
... | r′ , refl , wm = radec r′ , wm , bisim′-from o r′
bisim′ˢ-from o r .bwd .on-ev {l = evl e} step with o .oev r step
... | r′ , refl , wm = radec r′ , wm , bisim′-from o r′
bisim′ˢ-from o r .bwd .on-ev {l = √ x}  step = o .osqrt r step
bisim′ˢ-from o r .div→ d = o .odiv← r d
bisim′ˢ-from o r .div← d = o .odiv→ r d

-- `bisim′` at the initial reachable config (the whole-`SysState` bisim at
-- `initial`, given the oracle).  `rdec rinit ≡ ⟦ initial ⟧`, `radec rinit ≡
-- absDec initial` (both `refl`, inherited from R1/R2 home equalities).
bisim′-init : StepOracle → ⟦ initial ⟧ ≈DR absDec initial
bisim′-init o = bisim′-from o rinit

-- HEADLINE (modulo the oracle): `sysBisim = syswire (bisim′ rinit)` — the final
-- `dec-init`/`absDec-init` rewrite applied to the walker at `rinit`.  Once D3
-- populates the `StepOracle`, `sysBisim = sysBisim-from theOracle`.
sysBisim-from : StepOracle → systemBroken blkA ≈DR abstractSystem
sysBisim-from o = syswire (bisim′-init o)

------------------------------------------------------------------------
-- REACHABLE-PACKAGING (the hole-free, reusable half of each oracle entry).
--
-- A decoded co-move `st : toSys r ↝ s′` (the reflect-half's output — built for
-- a transition class from the generic `SysStep` seals: `lift-*-whole-τ` +
-- `absRun-*`/`*-sil-collapse` for the τ classes, `lift-*-whole-ev` for the api/
-- break classes, `lift-io-sync-whole-τ` for the hidden io-sync class) packages
-- DIRECTLY into an oracle output for the step `cstep st`: the reachable target
-- is `rclose r st` (definitional `refl`), the leaf inversion `⟦ s′ ⟧ ≡ rdec r′`
-- is `sym` of `rclose`'s equality, and the abstract weak match `radec r ═[l]═►
-- radec r′` is `amatch st` (since `radec r′ ≡ absDec s′` by `rclose-abs`, `refl`).
-- These close the "package Reachable + recurse guarded" half for EACH direction,
-- hole-free; D3 supplies the co-move (the reflect half) per transition class.
------------------------------------------------------------------------

-- forward τ classes (a: peer-internal sil ; b: shared-medium sil ; d: hidden
-- io-sync): a τ-labelled co-move packages into the `otau` output at the step it
-- witnesses.  `run` is `amatch st` after its label is fixed to `τ` (D3-supplied).
comove→otau : (r : RState) {s′ : _}
    (st : toSys r ↝ s′)
    (run : radec r ═[ τ ]═► radec (proj₁ (rclose r st)))
  → Σ[ r′ ∈ RState ] ((⟦ s′ ⟧ ≡ rdec r′) × (radec r ═[ τ ]═► radec r′))
comove→otau r st run = proj₁ (rclose r st) , sym (proj₂ (rclose r st)) , run

-- forward visible class (c: api sync / break medium-solo): an `ev`-labelled
-- co-move packages into the `oev` output
comove→oev : (r : RState) {s′ : _} {l : Event√ (⊤ {0ℓ})}
    (st : toSys r ↝ s′)
    (run : radec r ═[ ev l ]═► radec (proj₁ (rclose r st)))
  → Σ[ r′ ∈ RState ] ((⟦ s′ ⟧ ≡ rdec r′) × (radec r ═[ ev l ]═► radec r′))
comove→oev r st run = proj₁ (rclose r st) , sym (proj₂ (rclose r st)) , run

-- backward τ class (abstract τ matched by a concrete weak-τ run — the `bwd`
-- mirror): a τ co-move packages into the `otauB` output.  `absDec s′ ≡ radec r′`
-- is `rclose-abs` (refl); the concrete match `run` is `cstep`'s weak run.
comove→otauB : (r : RState) {s′ : _}
    (st : toSys r ↝ s′)
    (run : rdec r ═[ τ ]═► rdec (proj₁ (rclose r st)))
  → Σ[ r′ ∈ RState ] ((absDec s′ ≡ radec r′) × (rdec r ═[ τ ]═► rdec r′))
comove→otauB r st run = proj₁ (rclose r st) , sym (rclose-abs r st) , run

-- backward visible class (abstract api/break matched by the concrete event):
-- an `ev` co-move packages into the `oevB` output
comove→oevB : (r : RState) {s′ : _} {l : Event√ (⊤ {0ℓ})}
    (st : toSys r ↝ s′)
    (run : rdec r ═[ ev l ]═► rdec (proj₁ (rclose r st)))
  → Σ[ r′ ∈ RState ] ((absDec s′ ≡ radec r′) × (rdec r ═[ ev l ]═► rdec r′))
comove→oevB r st run = proj₁ (rclose r st) , sym (rclose-abs r st) , run

------------------------------------------------------------------------
-- REPRESENTATIVE co-move BUILDERS (the reflect-half's whole-system assembly).
--
-- These are the "reflect step → target `SysState s′` + concrete/abstract match"
-- half, EXHIBITED end-to-end for one representative transition class per
-- category, hole-free.  They are parametric ONLY in the LEAF step (the
-- per-component reduction the D3 grind supplies — a nodes/medium `─[l]─►`) and
-- the small definitional equalities (`med`/`nodes`/`absDec` unchanged on the
-- inert side).  The concrete/abstract whole-system steps are assembled by the
-- operand-generic `SysStep` seals APPLIED at the real `decMed`/`nodesOf`/
-- `absNodesOf` operands (opaque — no peer WHNF, seconds).  The result `s ↝ s′`
-- feeds `rclose` (in the oracle) and the `comove→o*` packagers above, then
-- `bisim′-from` recurses GUARDED.  D3's remaining job per class is exactly to
-- CONSTRUCT the leaf step + these equalities (the per-position FSM inversion).
------------------------------------------------------------------------

-- CATEGORY (a) — peer-internal sil (forward-τ, abstract 0-τ).  A NODES τ (a peer
-- loop re-entry sil) advances `⟦ s ⟧ → ⟦ s′ ⟧` leaving the medium fixed; the
-- τ-free abstract decode is UNCHANGED (`absEq` — the coarsening collapse,
-- `refl` at the concrete leaf), so the abstract side matches by ZERO τ.
comove-nodes-τ : (s s′ : SysState)
    (nodesStep : nodesOf s ─[ τ ]─► nodesOf s′)
    (medEq  : med s ≡ med s′)
    (absEq  : absDec s ≡ absDec s′)
  → s ↝ s′
comove-nodes-τ s s′ nodesStep medEq absEq = mkStep τ cstep amatch
  where
    cstep : ⟦ s ⟧ ─[ τ ]─► ⟦ s′ ⟧
    cstep = subst (λ mm → ⟦ s ⟧ ─[ τ ]─► ((mm ∥⇘ ioES ⇙ nodesOf s′) ∖ ioES))
                  (cong decMed medEq)
                  (lift-nodes-whole-τ (decMed (med s)) (nodesOf s) nodesStep)
    amatch : absDec s ═[ τ ]═► absDec s′
    amatch = wτ (subst (λ z → absDec s ─[τ*]─► z) absEq τ*-refl)

-- CATEGORY (b) — shared-medium sil (forward-τ, abstract matching τ).  A MEDIUM τ
-- (a copy cell's post-`output` `draining` loop-back sil) advances `⟦ s ⟧ → ⟦ s′ ⟧`
-- leaving the nodes fixed; the medium decode is SHARED verbatim, so the abstract
-- side does the IDENTICAL medium τ (one `wτ` step) via `lift-med-whole-τ` at the
-- abstract nodes operand.
comove-med-τ : (s s′ : SysState)
    (medStep : decMed (med s) ─[ τ ]─► decMed (med s′))
    (nodesEq     : nodesOf s ≡ nodesOf s′)
    (absNodesEq  : absNodesOf s ≡ absNodesOf s′)
  → s ↝ s′
comove-med-τ s s′ medStep nodesEq absNodesEq = mkStep τ cstep amatch
  where
    cstep : ⟦ s ⟧ ─[ τ ]─► ⟦ s′ ⟧
    cstep = subst (λ nn → ⟦ s ⟧ ─[ τ ]─► ((decMed (med s′) ∥⇘ ioES ⇙ nn) ∖ ioES))
                  nodesEq
                  (lift-med-whole-τ (decMed (med s)) (nodesOf s) medStep)
    amatch : absDec s ═[ τ ]═► absDec s′
    amatch = wτ (τ*-step
      (subst (λ nn → absDec s ─[ τ ]─► ((decMed (med s′) ∥⇘ ioES ⇙ nn) ∖ ioES))
             absNodesEq
             (lift-med-whole-τ (decMed (med s)) (absNodesOf s) medStep))
      τ*-refl)

-- CATEGORY (c) — api sync (forward AND backward visible).  A whole-system
-- VISIBLE event (an api driver↔peer sync surfacing as a nodes-solo event through
-- the io-gate, or a break medium-solo) advances `⟦ s ⟧ → ⟦ s′ ⟧`; the abstract
-- side (shared drivers/medium; spec peers syncing on the SAME api) does the
-- IDENTICAL single visible event, so both `═[ ev l ]═►` runs have ZERO padding τ
-- (`wev τ*-refl … τ*-refl`).  Parametric in the two assembled whole-system
-- visible steps (built by `lift-nodes-whole-ev` / `lift-med-whole-ev` at the
-- concrete resp. abstract operands — the reflect-half's per-class leaf work).
comove-ev : (s s′ : SysState) (l : Event√ (⊤ {0ℓ}))
    (cstep0 : ⟦ s ⟧ ─[ ev l ]─► ⟦ s′ ⟧)
    (astep0 : absDec s ─[ ev l ]─► absDec s′)
  → s ↝ s′
comove-ev s s′ l cstep0 astep0 =
  mkStep (ev l) cstep0 (wev τ*-refl astep0 τ*-refl)

-- CATEGORY (d) — hidden io-sync (forward-τ via `inner-io-single`).  A delivered
-- io `(e, a) ∈ ioES` is fired by BOTH the medium and its unique recipient node
-- (`inner-io-single` pins the recipient); `Hide-hidden` turns the sync into a
-- τ.  `lift-io-sync-whole-τ` assembles this whole-system τ; `⟦ s ⟧`/`absDec s`
-- share the medium verbatim, so the abstract side does the IDENTICAL io-sync τ
-- (one `wτ` step).  Parametric in the medium ev step + the concrete/abstract
-- recipient-node ev steps (the reflect-half's recipient pin — item-1b).
comove-io-sync : (s s′ : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    (iomem      : ioES .mem (X , e) a)
    (medEv      : decMed (med s) ─[ ev (evl (evLabel X e a)) ]─► decMed (med s′))
    (nodesEv    : nodesOf s      ─[ ev (evl (evLabel X e a)) ]─► nodesOf s′)
    (absNodesEv : absNodesOf s   ─[ ev (evl (evLabel X e a)) ]─► absNodesOf s′)
  → s ↝ s′
comove-io-sync s s′ iomem medEv nodesEv absNodesEv = mkStep τ cstep amatch
  where
    cstep : ⟦ s ⟧ ─[ τ ]─► ⟦ s′ ⟧
    cstep = lift-io-sync-whole-τ (decMed (med s)) (nodesOf s) iomem medEv nodesEv
    amatch : absDec s ═[ τ ]═► absDec s′
    amatch = wτ (τ*-step
      (lift-io-sync-whole-τ (decMed (med s)) (absNodesOf s) iomem medEv absNodesEv)
      τ*-refl)

-- CATEGORY (e) — divergence transfer.  There is NO dedicated co-move: `div→`/
-- `div←` are the `StepOracle` fields `odiv→`/`odiv←`.  The intended witness is
-- the measure `μ : SysState → ℕ` (from `SysStep`): every internal τ strictly
-- decreases `μ` (once the per-class τ-step characterizations of D3 land), so
-- neither decode admits an infinite τ-chain — `Diverges (rdec r)` is refutable
-- and the transfer is vacuous.  `μ` is re-exported here to mark the vehicle.
μSys : SysState → _
μSys = μ

------------------------------------------------------------------------
-- R2 D3 — the TOTAL `StepOracle.oev` field (`oev-impl`).  Dispatch a visible
-- top step of `rdec r = ⟦ toSys r ⟧` by its label: the `√` tick and every
-- non-api / non-break visible event are IMPOSSIBLE (SysRoute refutations); the
-- api class (apiCS/apiBF/done) is `top-api-comove`; `break` is `top-break-comove`.
-- The co-move output `(s′ , M ≡ ⟦ s′ ⟧ , abstract ev step)` is packaged into the
-- reachable oracle output via `comove-ev` + `rclose` (`pack-oev`).
------------------------------------------------------------------------

-- package a top-level visible co-move (s′ + M≡⟦s′⟧ + abstract ev step) into the
-- reachable `oev` output: `comove-ev` builds `toSys r ↝ s′`, `rclose` its successor
pack-oev : (r : RState) {l : Event√ (⊤ {0ℓ})} {M : NetProc}
    → rdec r ─[ ev l ]─► M
    → Σ[ s′ ∈ SysState ] (M ≡ ⟦ s′ ⟧) × (absDec (toSys r) ─[ ev l ]─► absDec s′)
    → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ ev l ]═► radec r′))
pack-oev r {l} step (s′ , Meq , astep0) =
  proj₁ (rclose r st) ,
  trans Meq (sym (proj₂ (rclose r st))) ,
  wev τ*-refl astep0 τ*-refl
  where
    cstep0 : ⟦ toSys r ⟧ ─[ ev l ]─► ⟦ s′ ⟧
    cstep0 = subst (λ z → ⟦ toSys r ⟧ ─[ ev l ]─► z) Meq step
    st : toSys r ↝ s′
    st = comove-ev (toSys r) s′ l cstep0 astep0

-- the `oev` field (visible NON-√ class): a visible `evl` top step reflected to
-- its reachable successor + the matching abstract weak move (impossible labels
-- are `⊥`-eliminated).  The √ class is handled separately by `osqrt-impl` (a √
-- step targets `deadlock`, not any `rdec r′`, so it cannot live in `oev`).
oev-impl : (r : RState) {e : Event} {M : NetProc} → rdec r ─[ ev (evl e) ]─► M
  → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ ev (evl e) ]═► radec r′))
oev-impl r {evLabel _ (apiCS l₀ d₀ m) a} step = pack-oev r step (SR.top-api-comove (toSys r) SO.aicCS tt step)
oev-impl r {evLabel _ (apiBF l₀ d₀ m) a} step = pack-oev r step (SR.top-api-comove (toSys r) SO.aicBF tt step)
oev-impl r {evLabel _ (done  l₀ d₀ id) a} step = pack-oev r step (SR.top-api-comove (toSys r) SO.aicDone tt step)
oev-impl r {evLabel _ (break l₀) a} step = pack-oev r step (SR.top-break-comove (toSys r) l₀ step)
oev-impl r {evLabel _ (input  l₀ d₀ id) a} step = ⊥-elim (SR.oev-no-io (toSys r) tt step)
oev-impl r {evLabel _ (output l₀ d₀ id) a} step = ⊥-elim (SR.oev-no-io (toSys r) tt step)
oev-impl r {evLabel _ (apiKA l₀ d₀ m) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-apiKA (med (toSys r))) (SR.nodes-no-nonCSBF (toSys r) tt (λ ())) step)
oev-impl r {evLabel _ (apiTS l₀ d₀ m) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-apiTS (med (toSys r))) (SR.nodes-no-nonCSBF (toSys r) tt (λ ())) step)
oev-impl r {evLabel _ (apiLN l₀ d₀ m) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-apiLN (med (toSys r))) (SR.nodes-no-nonCSBF (toSys r) tt (λ ())) step)
oev-impl r {evLabel _ (apiLF l₀ d₀ m) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-apiLF (med (toSys r))) (SR.nodes-no-nonCSBF (toSys r) tt (λ ())) step)
oev-impl r {evLabel _ (sndmsg l₀ d₀ id) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-sndmsg (med (toSys r))) (SR.nodes-no-sndmsg (toSys r)) step)
oev-impl r {evLabel _ (rcvmsg l₀ d₀ id) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-rcvmsg (med (toSys r))) (SR.nodes-no-rcvmsg (toSys r)) step)
oev-impl r {evLabel _ (tx     l₀ d₀ id) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-tx (med (toSys r))) (SR.nodes-no-tx (toSys r)) step)
oev-impl r {evLabel _ (sndack l₀ d₀ id) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-sndack (med (toSys r))) (SR.nodes-no-sndack (toSys r)) step)
oev-impl r {evLabel _ (rcvack l₀ d₀ id) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-rcvack (med (toSys r))) (SR.nodes-no-rcvack (toSys r)) step)
oev-impl r {evLabel _ (ack    l₀ d₀ id) a} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-ack (med (toSys r))) (SR.nodes-no-ack (toSys r)) step)

------------------------------------------------------------------------
-- R2 D3 — the TOTAL `StepOracle.otau` field (`otau-impl`).  A forward τ of
-- `rdec r = ⟦ toSys r ⟧` reflects (via `reflect-⟦⟧-τ`) into either an inner
-- `Par⊤ ioES` τ (further split by `reflect-inner-τ` into a MEDIUM τ or a NODES
-- τ) or a hidden io-SYNC.  Each class routes to a `SysState` successor `s′`
-- (medium-only / nodes-only / medium+nodes update), builds the whole-system
-- co-move (`comove-med-τ` / `comove-nodes-τ` / `comove-io-sync`), and packages
-- it into the `otau` output via `pack-otau` (`M ≡ rdec r′` + abstract weak-τ).
------------------------------------------------------------------------

-- package a τ co-move (`s′` + `M ≡ ⟦ s′ ⟧` + the co-move's abstract weak-τ run)
-- into the reachable `otau` output (mirror of `pack-oev`, on the τ side)
pack-otau : (r : RState) {M : NetProc} {s′ : SysState}
    (Meq : M ≡ ⟦ s′ ⟧)
    (st  : toSys r ↝ s′)
    (run : radec r ═[ τ ]═► radec (proj₁ (rclose r st)))
  → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ τ ]═► radec r′))
pack-otau r Meq st run = proj₁ (rclose r st) , trans Meq (sym (proj₂ (rclose r st))) , run

-- MEDIUM-τ branch: a copy cell drain (`draining → empty`) advances the medium
-- alone; `medium-τ-inv` reflects the `MedState` successor, nodes/abstract fixed.
otau-med : (r : RState) {M′ M : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ nodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ τ ]═► radec r′))
otau-med r {M′} {M} ms Meq with SIL.medium-τ-inv (med (toSys r)) ms
... | m′ , M′≡ =
      pack-otau r
        (trans Meq (cong (λ z → (z ∥⇘ ioES ⇙ nodesOf (toSys r)) ∖ ioES) M′≡))
        st (_↝_.amatch st)
  where
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    st : toSys r ↝ s′
    st = comove-med-τ (toSys r) s′
           (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms) refl refl

-- HIDDEN io-SYNC branch: a delivered io `(e,a) ∈ ioES` fired by BOTH the medium
-- (`medium-ev-inv`) and the unique recipient node (`top-nodes-io`, item 4);
-- combine into ONE `s′` (medium + nodes updated) and co-move via `comove-io-sync`.
otau-hidSync : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : nodesOf (toSys r) ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ τ ]═► radec r′))
otau-hidSync r {X}{e}{a}{M₁}{N₁}{M} iomem sM sN Meq
    with SIL.medium-ev-inv (med (toSys r)) iomem sM | SIL.top-nodes-io (toSys r) iomem sN
... | m′ , M₁≡ | s″ , _ , N₁≡ , absStep =
      pack-otau r
        (trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡))
        st (_↝_.amatch st)
  where
    s′ : SysState
    s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
    st : toSys r ↝ s′
    st = comove-io-sync (toSys r) s′ iomem
           (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM)
           (subst (λ z → nodesOf (toSys r) ─[ ev (evl (evLabel X e a)) ]─► z) N₁≡ sN)
           absStep

-- NODES-τ branch: a peer loop re-entry sil (`…Sil st → …Head st`) inside ONE of
-- the four nodes advances `nodesOf` alone; `reflect-nodes-τ` pins the moving node
-- and `SIL4.nodeX-τ-inv-abs` reflects its `NodeStateX` successor TOGETHER WITH the
-- abstract collapse (`absNodeX nX ≡ absNodeX nX′`), so the abstract side matches by
-- ZERO τ (`comove-nodes-τ`).  Medium/other-nodes fixed.
otau-nodes : (r : RState) {N′ M : NetProc}
    (ns  : nodesOf (toSys r) ─[ τ ]─► N′)
    (Meq : M ≡ ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N′) ∖ ioES))
  → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ τ ]═► radec r′))
otau-nodes r {N′} {M} ns Meq
    with reflect-nodes-τ (SN.decNodeA (nA (toSys r))) (SN.decNodeB (nB (toSys r)))
                         (SN.decNodeC (nC (toSys r))) (SN.decNodeD (nD (toSys r))) ns
... | nAτ A′ as eqA with SIL4.nodeA-τ-inv-abs (nA (toSys r)) as
...   | na′ , A′≡ , abseq =
        pack-otau r
          (trans Meq (cong (λ z → (decMed (med (toSys r)) ∥⇘ ioES ⇙ z) ∖ ioES) N′≡))
          st (_↝_.amatch st)
  where
    s′ : SysState
    s′ = mkSys (med (toSys r)) na′ (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    N′≡ : N′ ≡ nodesOf s′
    N′≡ = trans eqA (cong (λ z → z ⦀ (SN.decNodeB (nB (toSys r)) ⦀ (SN.decNodeC (nC (toSys r)) ⦀ SN.decNodeD (nD (toSys r))))) A′≡)
    st : toSys r ↝ s′
    st = comove-nodes-τ (toSys r) s′
           (subst (λ z → nodesOf (toSys r) ─[ τ ]─► z) N′≡ ns) refl
           (cong (λ z → (decMed (med (toSys r)) ∥⇘ ioES ⇙ (z ⦀ (absNodeB (nB (toSys r)) ⦀ (absNodeC (nC (toSys r)) ⦀ absNodeD (nD (toSys r)))))) ∖ ioES) abseq)
otau-nodes r {N′} {M} ns Meq | nBτ B′ bs eqB with SIL4.nodeB-τ-inv-abs (nB (toSys r)) bs
...   | nb′ , B′≡ , abseq =
        pack-otau r
          (trans Meq (cong (λ z → (decMed (med (toSys r)) ∥⇘ ioES ⇙ z) ∖ ioES) N′≡))
          st (_↝_.amatch st)
  where
    s′ : SysState
    s′ = mkSys (med (toSys r)) (nA (toSys r)) nb′ (nC (toSys r)) (nD (toSys r))
    N′≡ : N′ ≡ nodesOf s′
    N′≡ = trans eqB (cong (λ z → SN.decNodeA (nA (toSys r)) ⦀ (z ⦀ (SN.decNodeC (nC (toSys r)) ⦀ SN.decNodeD (nD (toSys r))))) B′≡)
    st : toSys r ↝ s′
    st = comove-nodes-τ (toSys r) s′
           (subst (λ z → nodesOf (toSys r) ─[ τ ]─► z) N′≡ ns) refl
           (cong (λ z → (decMed (med (toSys r)) ∥⇘ ioES ⇙ (absNodeA (nA (toSys r)) ⦀ (z ⦀ (absNodeC (nC (toSys r)) ⦀ absNodeD (nD (toSys r)))))) ∖ ioES) abseq)
otau-nodes r {N′} {M} ns Meq | nCτ C′ cs eqC with SIL4.nodeC-τ-inv-abs (nC (toSys r)) cs
...   | nc′ , C′≡ , abseq =
        pack-otau r
          (trans Meq (cong (λ z → (decMed (med (toSys r)) ∥⇘ ioES ⇙ z) ∖ ioES) N′≡))
          st (_↝_.amatch st)
  where
    s′ : SysState
    s′ = mkSys (med (toSys r)) (nA (toSys r)) (nB (toSys r)) nc′ (nD (toSys r))
    N′≡ : N′ ≡ nodesOf s′
    N′≡ = trans eqC (cong (λ z → SN.decNodeA (nA (toSys r)) ⦀ (SN.decNodeB (nB (toSys r)) ⦀ (z ⦀ SN.decNodeD (nD (toSys r))))) C′≡)
    st : toSys r ↝ s′
    st = comove-nodes-τ (toSys r) s′
           (subst (λ z → nodesOf (toSys r) ─[ τ ]─► z) N′≡ ns) refl
           (cong (λ z → (decMed (med (toSys r)) ∥⇘ ioES ⇙ (absNodeA (nA (toSys r)) ⦀ (absNodeB (nB (toSys r)) ⦀ (z ⦀ absNodeD (nD (toSys r)))))) ∖ ioES) abseq)
otau-nodes r {N′} {M} ns Meq | nDτ D′ ds eqD with SIL4.nodeD-τ-inv-abs (nD (toSys r)) ds
...   | nd′ , D′≡ , abseq =
        pack-otau r
          (trans Meq (cong (λ z → (decMed (med (toSys r)) ∥⇘ ioES ⇙ z) ∖ ioES) N′≡))
          st (_↝_.amatch st)
  where
    s′ : SysState
    s′ = mkSys (med (toSys r)) (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) nd′
    N′≡ : N′ ≡ nodesOf s′
    N′≡ = trans eqD (cong (λ z → SN.decNodeA (nA (toSys r)) ⦀ (SN.decNodeB (nB (toSys r)) ⦀ (SN.decNodeC (nC (toSys r)) ⦀ z))) D′≡)
    st : toSys r ↝ s′
    st = comove-nodes-τ (toSys r) s′
           (subst (λ z → nodesOf (toSys r) ─[ τ ]─► z) N′≡ ns) refl
           (cong (λ z → (decMed (med (toSys r)) ∥⇘ ioES ⇙ (absNodeA (nA (toSys r)) ⦀ (absNodeB (nB (toSys r)) ⦀ (absNodeC (nC (toSys r)) ⦀ z)))) ∖ ioES) abseq)

-- the TOTAL `otau` field: reflect a forward τ of `rdec r = ⟦ toSys r ⟧` and route
-- it to the medium / nodes / hidden-io-sync branch.  `reflect-⟦⟧-τ` splits into
-- an inner `Par⊤ ioES` τ (further `reflect-inner-τ` = MEDIUM vs NODES) or a hidden
-- io-SYNC; all three branches close (no impossible τ class).
otau-impl : (r : RState) {M : NetProc} → rdec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ τ ]═► radec r′))
otau-impl r step with reflect-⟦⟧-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (nodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = otau-med   r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = otau-nodes r ns (trans Peq (cong (λ z → z ∖ ioES) eqP))
otau-impl r step | hidSync M₁ N₁ iomem sM sN Peq = otau-hidSync r iomem sM sN Peq

------------------------------------------------------------------------
-- R2 D3 (D2-backward foundation) — WEAK-RUN LIFTS for the `oevB`/`otauB`
-- fields.  A backward abstract step is matched by a concrete WEAK run whose
-- padding τ's come from `csSil` loop-re-entry peers (a sil-positioned peer must
-- first do its loop-back τ before firing).  These lift a COMPONENT weak run up
-- the whole-system `∥⇘ ioES ⇙` / `∖ ioES` stack.  (The single-step versions
-- `lift-*-whole-*` cannot express the padding; hence the weak analogues.)
------------------------------------------------------------------------

-- a `τ*` run survives hide `∖ A`
∖-τ*w : (A : EventSet) (P : NetProc) {P′ : NetProc}
      → P ─[τ*]─► P′ → (P ∖ A) ─[τ*]─► (P′ ∖ A)
∖-τ*w A P τ*-refl          = τ*-refl
∖-τ*w A P (τ*-step s rest) = τ*-step (∖-τ A P s) (∖-τ*w A _ rest)

-- a WEAK visible run of an event ∉ A survives hide `∖ A` (event stays visible)
∖-wev : (A : EventSet) (P : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {P′ : NetProc}
      → ¬ A .mem (X , e) a
      → P ═[ ev (evl (evLabel X e a)) ]═► P′
      → (P ∖ A) ═[ ev (evl (evLabel X e a)) ]═► (P′ ∖ A)
∖-wev A P ¬mem (wev {p′ = P₁} {q′ = P₂} pre fire post) =
  wev (∖-τ*w A P pre) (∖-ev A P₁ ¬mem fire) (∖-τ*w A P₂ post)

-- lift a NODES weak visible run (event ∉ ioES) up to the whole system, medium fixed
lift-nodes-whole-wev : (Med Nodes : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Nodes′ : NetProc}
    → ¬ ioES .mem (X , e) a
    → viewV (PTree.force Med) (X , e) a ≡ nothing
    → Nodes ═[ ev (evl (evLabel X e a)) ]═► Nodes′
    → ((Med ∥⇘ ioES ⇙ Nodes)  ∖ ioES) ═[ ev (evl (evLabel X e a)) ]═► ((Med ∥⇘ ioES ⇙ Nodes′) ∖ ioES)
lift-nodes-whole-wev Med Nodes ¬mem nq wrun =
  ∖-wev ioES (Med ∥⇘ ioES ⇙ Nodes) ¬mem (SIL6.∥⇘⇙-wev-soloR ioES Med Nodes ¬mem nq wrun)

-- lift a synchronised medium+nodes WEAK io run up to a whole-system WEAK τ run
-- (the io ∈ ioES sync is HIDDEN by `∖ ioES`, so the fire step becomes a τ)
lift-io-sync-whole-wτ : (Med Nodes : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Med′ Nodes′ : NetProc}
    → ioES .mem (X , e) a
    → Med   ═[ ev (evl (evLabel X e a)) ]═► Med′
    → Nodes ═[ ev (evl (evLabel X e a)) ]═► Nodes′
    → ((Med ∥⇘ ioES ⇙ Nodes) ∖ ioES) ═[ τ ]═► ((Med′ ∥⇘ ioES ⇙ Nodes′) ∖ ioES)
lift-io-sync-whole-wτ Med Nodes iomem wM wN with SIL6.∥⇘⇙-wev-sync ioES Med Nodes iomem wM wN
... | wev {p′ = P₁} {q′ = P₂} pre fire post =
      wτ (τ*-trans (∖-τ*w ioES _ pre)
           (τ*-step (Hide-hidden ioES P₁ iomem fire) (∖-τ*w ioES P₂ post)))

------------------------------------------------------------------------
-- BACKWARD REACHABLE-PACKAGERS (mirror `pack-oev`/`pack-otau`, but on the
-- backward side: the abstract step is PRIMARY, and the reachable successor is
-- certified from a concrete WEAK run via `rcloseʷ` — SysReach's closure under
-- weak decode runs).  `Meq : M ≡ absDec s′` identifies the abstract target;
-- `wrun` is the concrete weak run into `⟦ s′ ⟧`.
------------------------------------------------------------------------

-- package a backward VISIBLE co-move into the `oevB` output via `rcloseʷ`
pack-oevB : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc} {s′ : SysState}
    (Meq  : M ≡ absDec s′)
    (wrun : rdec r ═[ ev (evl (evLabel X e a)) ]═► ⟦ s′ ⟧)
  → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′))
pack-oevB r {X} {e} {a} {s′ = s′} Meq wrun =
  proj₁ (rcloseʷ r {s′ = s′} wrun) ,
  trans Meq (sym (rcloseʷ-abs r {s′ = s′} wrun)) ,
  subst (λ z → rdec r ═[ ev (evl (evLabel X e a)) ]═► z) (sym (proj₂ (rcloseʷ r {s′ = s′} wrun))) wrun

-- package a backward τ co-move into the `otauB` output via `rcloseʷ`
pack-otauB : (r : RState) {M : NetProc} {s′ : SysState}
    (Meq  : M ≡ absDec s′)
    (wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧)
  → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ τ ]═► rdec r′))
pack-otauB r {s′ = s′} Meq wrun =
  proj₁ (rcloseʷ r {s′ = s′} wrun) ,
  trans Meq (sym (rcloseʷ-abs r {s′ = s′} wrun)) ,
  subst (λ z → rdec r ═[ τ ]═► z) (sym (proj₂ (rcloseʷ r {s′ = s′} wrun))) wrun

------------------------------------------------------------------------
-- R2 D3 — the TOTAL `StepOracle.otauB` field (`otauB-impl`).  An abstract τ of
-- `radec r = absDec (toSys r)` reflects (via `reflect-absDec-τ`) into an inner
-- `∥⇘ ioES ⇙` τ (MEDIUM vs abstract-NODES) or a hidden io-SYNC.  The abstract
-- nodes are native-react τ-free, so the NODES branch is VACUOUS; the MEDIUM τ is
-- matched by the IDENTICAL concrete medium τ (shared, single step); the io-sync
-- is matched by a concrete WEAK τ run (`top-nodes-io-abs`, padded).
------------------------------------------------------------------------

-- MEDIUM-τ branch: abstract medium τ matched by the IDENTICAL concrete medium τ
otauB-med : (r : RState) {M′ M : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ τ ]═► rdec r′))
otauB-med r {M′} {M} ms Meq with SIL.medium-τ-inv (med (toSys r)) ms
... | m′ , M′≡ = pack-otauB r {s′ = s′} Meq′ wrun
  where
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    Meq′ : M ≡ absDec s′
    Meq′ = trans Meq (cong (λ z → (z ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES) M′≡)
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = wτ (τ*-step
             (lift-med-whole-τ (decMed (med (toSys r))) (nodesOf (toSys r))
               (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms))
             τ*-refl)

-- HIDDEN io-SYNC branch: abstract io fired by BOTH the (shared) medium and a
-- unique abstract recipient node; concrete matches with a WEAK τ run (the
-- concrete recipient run from `top-nodes-io-abs` is padded by sil loop-backs).
otauB-hidSync : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ τ ]═► rdec r′))
otauB-hidSync r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with SIL.medium-ev-inv (med (toSys r)) iomem sM | SIL6.top-nodes-io-abs (toSys r) iomem sN
... | m′ , M₁≡ | s″ , medEq , N₁≡ , cWeakRun = pack-otauB r {s′ = s′} Meq′ wrun
  where
    s′ : SysState
    s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
    Meq′ : M ≡ absDec s′
    Meq′ = trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡)
    medWeak : decMed (med (toSys r)) ═[ ev (evl (evLabel X e a)) ]═► decMed m′
    medWeak = wev τ*-refl (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM) τ*-refl
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = lift-io-sync-whole-wτ (decMed (med (toSys r))) (nodesOf (toSys r)) iomem medWeak cWeakRun

-- the TOTAL `otauB` field: reflect an abstract τ of `radec r = absDec (toSys r)`
-- and route it to the medium / VACUOUS-nodes / hidden-io-sync branch.
otauB-impl : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ τ ]═► rdec r′))
otauB-impl r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = otauB-med r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (SNT.absNodesOf-no-τ (toSys r) ns)
otauB-impl r step | hidSync M₁ N₁ iomem sM sN Peq = otauB-hidSync r iomem sM sN Peq

------------------------------------------------------------------------
-- R2 D3 — the `StepOracle.oevB` field (`oevB-impl`).  An abstract visible
-- event of `radec r = absDec (toSys r)` is peeled by `reflect-top-ev` at the
-- ABSTRACT operands (`decMed (med s)` / `absNodesOf s`) into a medium solo
-- (`break`) or a nodes solo (api).  The api class routes through the backward
-- abstract node peel `top-nodes-abs` (a PADDED concrete weak run — `csSil`
-- loop-backs — packaged via `rcloseʷ`); `break` is a single shared-medium step;
-- io is HIDDEN (refuted); the remaining labels are refuted at medium+nodes.
------------------------------------------------------------------------

-- api class (apiCS/apiBF/done): abstract nodes-solo peeled by `top-nodes-abs`,
-- the concrete weak run lifted up the medium-fixed `∥⇘ ioES ⇙`/`∖ ioES` stack
oevB-api : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → SO.IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′))
oevB-api r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | SStep.medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | SStep.nodesEv N₁ ns refl with SIL6.top-nodes-abs (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun = pack-oevB r {s′ = s′} Meq′ wrun
  where
    Meq′ : ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N₁) ∖ ioES) ≡ absDec s′
    Meq′ = cong₂ (λ mm nn → (decMed mm ∥⇘ ioES ⇙ nn) ∖ ioES) medEq N₁≡
    wrun : rdec r ═[ ev (evl (evLabel X e a)) ]═► ⟦ s′ ⟧
    wrun = subst (λ mm → rdec r ═[ ev (evl (evLabel X e a)) ]═► ((decMed mm ∥⇘ ioES ⇙ nodesOf s′) ∖ ioES))
             medEq
             (lift-nodes-whole-wev (decMed (med (toSys r))) (nodesOf (toSys r))
               (SR.api∉ioES {X} {e} {a} aic)
               (GB.noOffer→viewV _ (SR.medium-api-non-offer (med (toSys r)) aic))
               cWeakRun)

-- break class: abstract medium-solo `break`, matched by the IDENTICAL concrete
-- medium break (medium SHARED, single visible step; zero padding)
oevB-break : (r : RState) (l : Link) {a : ⊤₀} {M : NetProc}
  → radec r ─[ ev (evl (evLabel ⊤₀ (break l) a)) ]─► M
  → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► rdec r′))
oevB-break r l {a} step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₂ (SR.absnodes-no-break (toSys r))) step
... | SStep.nodesEv N₁ ns _ = ⊥-elim (SR.absnodes-no-break (toSys r) (N₁ , ns))
... | SStep.medEv M₁ medStep refl with SR.medium-break-ev-inv (med (toSys r)) l medStep
...   | m′ , refl = pack-oevB r {s′ = s′} refl wrun
  where
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    wrun : rdec r ═[ ev (evl (evLabel ⊤₀ (break l) a)) ]═► ⟦ s′ ⟧
    wrun = wev τ*-refl
             (SStep.lift-med-whole-ev (decMed (med (toSys r))) (nodesOf (toSys r))
               (SR.break∉ioES {l} {a}) medStep
               (GB.noOffer→viewV _ (SR.nodes-no-break (toSys r))))
             τ*-refl

-- io class (input/output ∈ ioES): a visible io of `absDec r` is IMPOSSIBLE (io
-- is HIDDEN by `∖ ioES` — the `Hide-ev-elim` `keep` carries `¬ (io ∈ ioES)`)
oevB-no-io : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a → radec r ─[ ev (evl (evLabel X e a)) ]─► M → ⊥
oevB-no-io r iomem step
  with Hide-ev-elim ioES (decMed (med (toSys r)) ∥⇘ ioES ⇙ absNodesOf (toSys r)) step
... | heV P′ ¬mem _ = ¬mem iomem

-- generic abstract top-level refutation: an event offered by NEITHER the medium
-- NOR the abstract nodes cannot fire from `absDec r` (mirror of `oev-refute`)
oevB-refute : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ¬ IoOffers (decMed (med (toSys r))) e a → ¬ IoOffers (absNodesOf (toSys r)) e a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M → ⊥
oevB-refute r mno nno step
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r)) (inj₁ mno) step
... | SStep.medEv M₁ ms _   = mno (M₁ , ms)
... | SStep.nodesEv N₁ ns _ = nno (N₁ , ns)

-- the `oevB` field (backward visible NON-√ class): dispatch an abstract visible
-- `evl` top step of `radec r = absDec (toSys r)` by its label.  api (apiCS/apiBF/
-- done) → `oevB-api`; `break` → `oevB-break`; io (input/output ∈ ioES) is HIDDEN
-- (`oevB-no-io`); the inert api events (apiKA/apiTS/apiLN/apiLF) and the wire
-- messages (sndmsg/…/ack) are IMPOSSIBLE — refuted at medium (`SR.medium-no-X`)
-- and abstract nodes (`SR.absnodes-no-nonCSBF` / `SR.absnodes-no-<msg>`).  The
-- byte-mirror of `oev-impl`; the √ class lives in `osqrtB` (separate field).
oevB-impl : (r : RState) {e : Event} {M : NetProc} → radec r ─[ ev (evl e) ]─► M
  → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ ev (evl e) ]═► rdec r′))
oevB-impl r {evLabel _ (apiCS l₀ d₀ m) a} step = oevB-api r SO.aicCS tt step
oevB-impl r {evLabel _ (apiBF l₀ d₀ m) a} step = oevB-api r SO.aicBF tt step
oevB-impl r {evLabel _ (done  l₀ d₀ id) a} step = oevB-api r SO.aicDone tt step
oevB-impl r {evLabel _ (break l₀) a} step = oevB-break r l₀ step
oevB-impl r {evLabel _ (input  l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
oevB-impl r {evLabel _ (output l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
oevB-impl r {evLabel _ (apiKA l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiKA (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
oevB-impl r {evLabel _ (apiTS l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiTS (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
oevB-impl r {evLabel _ (apiLN l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLN (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
oevB-impl r {evLabel _ (apiLF l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLF (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
oevB-impl r {evLabel _ (sndmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndmsg (med (toSys r))) (SR.absnodes-no-sndmsg (toSys r)) step)
oevB-impl r {evLabel _ (rcvmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvmsg (med (toSys r))) (SR.absnodes-no-rcvmsg (toSys r)) step)
oevB-impl r {evLabel _ (tx     l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-tx (med (toSys r))) (SR.absnodes-no-tx (toSys r)) step)
oevB-impl r {evLabel _ (sndack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndack (med (toSys r))) (SR.absnodes-no-sndack (toSys r)) step)
oevB-impl r {evLabel _ (rcvack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvack (med (toSys r))) (SR.absnodes-no-rcvack (toSys r)) step)
oevB-impl r {evLabel _ (ack    l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-ack (med (toSys r))) (SR.absnodes-no-ack (toSys r)) step)

------------------------------------------------------------------------
-- R2 D3 — the TOTAL `StepOracle.osqrt` field (`osqrt-impl`).  The FORWARD √
-- CO-MOVE.  A concrete √ is `sRet eqf : rdec r ─[ ev (√ x) ]─► deadlock` with
-- `eqf : force (rdec r) ≡ ret x` (`M = deadlock`).  `SS.sys-ret-transfer`
-- transports the whole-system `ret` from the concrete to the abstract decode
-- (all peers sit at their `xHead stDone`/`kcTermE1` ret positions — a concrete
-- `ret` rules out every `xSil` position), so the abstract side also rets and
-- fires the SAME √ (`sRet`, zero padding).  The residual is the terminal
-- `deadlock ≈DR deadlock` (`drbisim-refl deadlock`).
------------------------------------------------------------------------
osqrt-impl : (r : RState) {x : ⊤ {0ℓ}} {M : NetProc} → rdec r ─[ ev (√ x) ]─► M
           → Σ[ t′ ∈ NetProc ] ((radec r ═[ ev (√ x) ]═► t′) × DRbisim (⊤ {0ℓ}) M t′)
osqrt-impl r (sRet eqf) =
  deadlock , wev τ*-refl (sRet (sys-ret-transfer r eqf)) τ*-refl , drbisim-refl deadlock

------------------------------------------------------------------------
-- R2 D3 — whole-system BACKWARD weak-ret (the `osqrtB` leaf).  The abstract
-- decode `radec r` rets ⇒ the concrete decode `rdec r` WEAK-runs (τ*) to a
-- `ret`.  Both share `decMed` (which rets); only the nodes differ, bridged by
-- `SS.nodes-wret` (which τ*-collapses any pending `xSil` peers).  The nodes
-- weak run is lifted up the medium-fixed `∥⇘ ioES ⇙` (`SS.∥⇘⇙-τ*-R`) and the
-- hide `∖ ioES` (`∖-τ*w`); the target's `ret` is `fHide-ret ∘ ∥⇙-ret-intro`.
------------------------------------------------------------------------
sys-wret : (r : RState) → force (radec r) ≡ ret tt
         → Σ[ P ∈ NetProc ] (rdec r ─[τ*]─► P) × (force P ≡ ret tt)
sys-wret r eq =
  let absInner : force (decMed (med (toSys r)) ∥⇘ ioES ⇙ absNodesOf (toSys r)) ≡ ret tt
      absInner = fHide-ret-inv {P = decMed (med (toSys r)) ∥⇘ ioES ⇙ absNodesOf (toSys r)} {A = ioES} eq
      medR     = proj₁ (∥⇙-ret-inv {A = ioES} {P = decMed (med (toSys r))} {Q = absNodesOf (toSys r)} absInner)
      absNodesR = proj₂ (∥⇙-ret-inv {A = ioES} {P = decMed (med (toSys r))} {Q = absNodesOf (toSys r)} absInner)
      Pn , runN , fN = nodes-wret (toSys r) absNodesR
  in ((decMed (med (toSys r)) ∥⇘ ioES ⇙ Pn) ∖ ioES)
   , ∖-τ*w ioES (decMed (med (toSys r)) ∥⇘ ioES ⇙ nodesOf (toSys r))
       (∥⇘⇙-τ*-R ioES (decMed (med (toSys r))) (nodesOf (toSys r)) runN)
   , fHide-ret {P = decMed (med (toSys r)) ∥⇘ ioES ⇙ Pn} {A = ioES}
       (∥⇙-ret-intro {A = ioES} {P = decMed (med (toSys r))} {Q = Pn} medR fN)

------------------------------------------------------------------------
-- R2 D3 — the TOTAL `StepOracle.osqrtB` field (`osqrtB-impl`).  The BACKWARD
-- √ CO-MOVE.  An abstract √ is `sRet eqf : radec r ─[ ev (√ x) ]─► deadlock`
-- with `eqf : force (radec r) ≡ ret x`.  `sys-wret` τ*-collapses the concrete
-- pending `xSil` peers to a `ret` (the reachable √-asymmetry, documented in
-- `SysSqrt`), whence the concrete side fires the SAME √ as a WEAK run `wev
-- (pad) (sRet …) τ*-refl`.  Residual `deadlock ≈DR deadlock`.
------------------------------------------------------------------------
osqrtB-impl : (r : RState) {x : ⊤ {0ℓ}} {M : NetProc} → radec r ─[ ev (√ x) ]─► M
            → Σ[ t′ ∈ NetProc ] ((rdec r ═[ ev (√ x) ]═► t′) × DRbisim (⊤ {0ℓ}) M t′)
osqrtB-impl r (sRet eqf) =
  let Pn , pad , fn = sys-wret r eqf
  in deadlock , wev pad (sRet fn) τ*-refl , drbisim-refl deadlock

------------------------------------------------------------------------
-- R2 D3 — the BACKWARD divergence transfer `odiv←` (`Diverges (radec r) →
-- Diverges (rdec r)`).  Every abstract τ reflects (via `reflect-absDec-τ`) to a
-- MEDIUM τ (a single shared concrete τ) or a HIDDEN io-SYNC (≥1 concrete τ:
-- the io fire, possibly preceded by concrete sil loop-backs); the abstract
-- NODES are native-react τ-free (`absNodesOf-no-τ`), so that branch is VACUOUS.
-- Hence EACH abstract τ produces a concrete WEAK τ run with AT LEAST ONE step,
-- exposed in SPLIT form (first single τ + a `τ*` tail) by `otauB-split`.  The
-- coinductive engine `divChain` walks that `τ*` tail then restarts on the next
-- abstract τ; because the first τ is always present, the corecursive call is
-- GUARDED (directly under `.Diverges.rest`) and NO measure is needed.
------------------------------------------------------------------------

-- split a `τ*`-then-`τ`-then-`τ*` run into a FIRST single τ + the remaining τ*
-- (always ≥1 step; the middle `b` is the guaranteed fire)
splitTransStep : {P Q Q′ S : NetProc}
    (A : P ─[τ*]─► Q) (b : Q ─[ τ ]─► Q′) (C : Q′ ─[τ*]─► S)
  → Σ[ P₁ ∈ NetProc ] (P ─[ τ ]─► P₁) × (P₁ ─[τ*]─► S)
splitTransStep τ*-refl                b C = _ , b , C
splitTransStep (τ*-step {t′ = P₁} s A′) b C = P₁ , s , τ*-trans A′ (τ*-step b C)

-- lift a synchronised medium+nodes WEAK io run to a whole-system τ, exposed as a
-- FIRST single τ + a `τ*` tail (split of `lift-io-sync-whole-wτ`, always ≥1 step)
lift-io-sync-whole-wτ-split : (Med Nodes : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Med′ Nodes′ : NetProc}
    → ioES .mem (X , e) a
    → Med   ═[ ev (evl (evLabel X e a)) ]═► Med′
    → Nodes ═[ ev (evl (evLabel X e a)) ]═► Nodes′
    → Σ[ P₁ ∈ NetProc ]
        (((Med ∥⇘ ioES ⇙ Nodes) ∖ ioES) ─[ τ ]─► P₁)
      × (P₁ ─[τ*]─► ((Med′ ∥⇘ ioES ⇙ Nodes′) ∖ ioES))
lift-io-sync-whole-wτ-split Med Nodes iomem wM wN with SIL6.∥⇘⇙-wev-sync ioES Med Nodes iomem wM wN
... | wev {p′ = P₁} {q′ = P₂} pre fire post =
      splitTransStep (∖-τ*w ioES _ pre) (Hide-hidden ioES P₁ iomem fire) (∖-τ*w ioES P₂ post)

-- package a SPLIT backward τ co-move (first τ + τ* tail into `⟦ s′ ⟧`) into the
-- reachable form: `rcloseʷ` certifies `s′` reachable from a reassembled weak run
pack-otauB-split : (r : RState) {M : NetProc} (s′ : SysState) {P₁ : NetProc}
    (Meq   : M ≡ absDec s′)
    (first : rdec r ─[ τ ]─► P₁)
    (rest* : P₁ ─[τ*]─► ⟦ s′ ⟧)
  → Σ[ r′ ∈ RState ] Σ[ Q ∈ NetProc ] (M ≡ radec r′) × (rdec r ─[ τ ]─► Q) × (Q ─[τ*]─► rdec r′)
pack-otauB-split r {M} s′ {P₁} Meq first rest* =
    proj₁ (rcloseʷ r {s′ = s′} wrun)
  , P₁
  , trans Meq (sym (rcloseʷ-abs r {s′ = s′} wrun))
  , first
  , rest*
  where
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = wτ (τ*-step first rest*)

-- MEDIUM-τ split branch: the concrete medium τ is a SINGLE step (τ* tail empty)
otauB-med-split : (r : RState) {M′ M : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] Σ[ Q ∈ NetProc ] (M ≡ radec r′) × (rdec r ─[ τ ]─► Q) × (Q ─[τ*]─► rdec r′)
otauB-med-split r {M′} {M} ms Meq with SIL.medium-τ-inv (med (toSys r)) ms
... | m′ , M′≡ = pack-otauB-split r s′ Meq′ first τ*-refl
  where
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    Meq′ : M ≡ absDec s′
    Meq′ = trans Meq (cong (λ z → (z ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES) M′≡)
    first : rdec r ─[ τ ]─► ⟦ s′ ⟧
    first = lift-med-whole-τ (decMed (med (toSys r))) (nodesOf (toSys r))
              (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms)

-- HIDDEN io-SYNC split branch: the concrete run is the split io-sync weak τ
otauB-hidSync-split : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] Σ[ Q ∈ NetProc ] (M ≡ radec r′) × (rdec r ─[ τ ]─► Q) × (Q ─[τ*]─► rdec r′)
otauB-hidSync-split r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with SIL.medium-ev-inv (med (toSys r)) iomem sM | SIL6.top-nodes-io-abs (toSys r) iomem sN
... | m′ , M₁≡ | s″ , medEq , N₁≡ , cWeakRun
    with lift-io-sync-whole-wτ-split (decMed (med (toSys r))) (nodesOf (toSys r)) iomem
           (wev τ*-refl (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM) τ*-refl)
           cWeakRun
...   | P₁ , first , rest* = pack-otauB-split r s′ Meq′ first rest*
  where
    s′ : SysState
    s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
    Meq′ : M ≡ absDec s′
    Meq′ = trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡)

-- the SPLIT abstract-τ reflector: every abstract τ yields a first concrete τ +
-- a τ* tail into `rdec r′` (mirror of `otauB-impl`; nodes branch VACUOUS)
otauB-split : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] Σ[ Q ∈ NetProc ] (M ≡ radec r′) × (rdec r ─[ τ ]─► Q) × (Q ─[τ*]─► rdec r′)
otauB-split r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = otauB-med-split r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (SNT.absNodesOf-no-τ (toSys r) ns)
otauB-split r step | hidSync M₁ N₁ iomem sM sN Peq = otauB-hidSync-split r iomem sM sN Peq

-- coinductive engine: walk a concrete `τ*` run to `rdec r`, then RESTART on the
-- next abstract τ (peeled by `otauB-split`, always ≥1 concrete τ) — so every
-- restart emits a `.step` first and the corecursive call is GUARDED
divChain : (P : NetProc) (r : RState)
         → P ─[τ*]─► rdec r → Diverges (radec r) → Diverges P
-- non-empty run prefix: emit the head τ, walk the tail (guarded under `.rest`)
divChain P r (τ*-step {t′ = Q} s rest) d .Diverges.next = Q
divChain P r (τ*-step {t′ = Q} s rest) d .Diverges.step = s
divChain P r (τ*-step {t′ = Q} s rest) d .Diverges.rest = divChain Q r rest d
-- run exhausted (`P = rdec r`): restart on the next abstract τ via `otauB-split`
divChain P r τ*-refl d .Diverges.next =
  proj₁ (proj₂ (otauB-split r (Diverges.step d)))
divChain P r τ*-refl d .Diverges.step =
  proj₁ (proj₂ (proj₂ (proj₂ (otauB-split r (Diverges.step d)))))
divChain P r τ*-refl d .Diverges.rest =
  divChain (proj₁ (proj₂ (otauB-split r (Diverges.step d))))
           (proj₁ (otauB-split r (Diverges.step d)))
           (proj₂ (proj₂ (proj₂ (proj₂ (otauB-split r (Diverges.step d))))))
           (subst Diverges (proj₁ (proj₂ (proj₂ (otauB-split r (Diverges.step d)))))
                  (Diverges.rest d))

-- the BACKWARD divergence transfer: kick off `divChain` with an empty concrete
-- run at `rdec r`, which immediately restarts on `d`'s first abstract τ
odiv←-impl : (r : RState) → Diverges (radec r) → Diverges (rdec r)
odiv←-impl r d = divChain (rdec r) r τ*-refl d

------------------------------------------------------------------------
-- R2 D3 — the FORWARD divergence transfer `odiv→` (`Diverges (rdec r) →
-- Diverges (radec r)`).  A concrete τ is either a NODES τ (a peer loop
-- re-entry sil — abstract does ZERO τ, `μ'Sys` strictly DROPS: a SKIP) or a
-- MEDIUM τ / hidden io-SYNC (abstract does exactly ONE τ: an EMIT).  The forward
-- classifier `otau-class` splits these; `skipToProd` walks finitely many SKIPs
-- (well-founded on `Acc _<_ (μ'Sys …)`) to the next EMIT; the coinductive
-- `divChainF` emits that abstract τ and corecurses GUARDED (under `.Diverges.rest`).
------------------------------------------------------------------------

-- forward-τ classification of a concrete `rdec r ─[ τ ]─► M`
data OtauClass (r : RState) (M : NetProc) : Set₁ where
  -- SKIP: a peer-sil nodes-τ — abstract UNCHANGED, `μ'Sys` strictly drops
  cskip : (r′ : RState) → M ≡ rdec r′ → radec r ≡ radec r′
        → μ'Sys (toSys r′) < μ'Sys (toSys r) → OtauClass r M
  -- EMIT: a medium-τ / io-sync — abstract makes exactly ONE τ
  cemit : (r′ : RState) → M ≡ rdec r′ → radec r ─[ τ ]─► radec r′ → OtauClass r M

-- MEDIUM-τ branch → EMIT (the medium is shared; abstract does the identical τ)
otau-class-med : (r : RState) {M′ M : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ nodesOf (toSys r)) ∖ ioES))
  → OtauClass r M
otau-class-med r {M′} {M} ms Meq with SIL.medium-τ-inv (med (toSys r)) ms
... | m′ , M′≡ = cemit (proj₁ (rclose r st)) Meq-r′ astep
  where
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    st : toSys r ↝ s′
    st = comove-med-τ (toSys r) s′
           (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms) refl refl
    Meq-r′ : M ≡ rdec (proj₁ (rclose r st))
    Meq-r′ = trans (trans Meq (cong (λ z → (z ∥⇘ ioES ⇙ nodesOf (toSys r)) ∖ ioES) M′≡))
                   (sym (proj₂ (rclose r st)))
    astep : radec r ─[ τ ]─► radec (proj₁ (rclose r st))
    astep = lift-med-whole-τ (decMed (med (toSys r))) (absNodesOf (toSys r))
              (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms)

-- HIDDEN io-SYNC branch → EMIT (the io fire is a shared τ on both sides)
otau-class-hidSync : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : nodesOf (toSys r) ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → OtauClass r M
otau-class-hidSync r {X}{e}{a}{M₁}{N₁}{M} iomem sM sN Meq
    with SIL.medium-ev-inv (med (toSys r)) iomem sM | SIL.top-nodes-io (toSys r) iomem sN
... | m′ , M₁≡ | s″ , _ , N₁≡ , absStep = cemit (proj₁ (rclose r st)) Meq-r′ astep
  where
    s′ : SysState
    s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
    st : toSys r ↝ s′
    st = comove-io-sync (toSys r) s′ iomem
           (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM)
           (subst (λ z → nodesOf (toSys r) ─[ ev (evl (evLabel X e a)) ]─► z) N₁≡ sN)
           absStep
    Meq-r′ : M ≡ rdec (proj₁ (rclose r st))
    Meq-r′ = trans (trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡))
                   (sym (proj₂ (rclose r st)))
    astep : radec r ─[ τ ]─► radec (proj₁ (rclose r st))
    astep = lift-io-sync-whole-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) iomem
              (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM)
              absStep

-- NODES-τ branch → SKIP (a peer sil; abstract unchanged, `μ'Sys` drops)
otau-class-nodes : (r : RState) {N′ M : NetProc}
    (ns  : nodesOf (toSys r) ─[ τ ]─► N′)
    (Meq : M ≡ ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N′) ∖ ioES))
  → OtauClass r M
otau-class-nodes r {N′} {M} ns Meq with SD.nodes-τ-μ'↓ (toSys r) ns
... | s′ , N′≡ , medEq , absEq , μ↓ = cskip (proj₁ (rclose r st)) Meq-r′ radec-eq μ↓
  where
    absDecEq : absDec (toSys r) ≡ absDec s′
    absDecEq = cong₂ (λ m n → (decMed m ∥⇘ ioES ⇙ n) ∖ ioES) medEq absEq
    st : toSys r ↝ s′
    st = comove-nodes-τ (toSys r) s′
           (subst (λ z → nodesOf (toSys r) ─[ τ ]─► z) N′≡ ns) medEq absDecEq
    Meq-r′ : M ≡ rdec (proj₁ (rclose r st))
    Meq-r′ = trans (trans Meq (cong₂ (λ m n → (decMed m ∥⇘ ioES ⇙ n) ∖ ioES) medEq N′≡))
                   (sym (proj₂ (rclose r st)))
    radec-eq : radec r ≡ radec (proj₁ (rclose r st))
    radec-eq = trans absDecEq (sym (rclose-abs r st))

-- the forward classifier: reflect a concrete τ and route it to SKIP/EMIT
otau-class : (r : RState) {M : NetProc} → rdec r ─[ τ ]─► M → OtauClass r M
otau-class r step with reflect-⟦⟧-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (nodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = otau-class-med   r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = otau-class-nodes r ns (trans Peq (cong (λ z → z ∖ ioES) eqP))
otau-class r step | hidSync M₁ N₁ iomem sM sN Peq = otau-class-hidSync r iomem sM sN Peq

-- INDUCTIVE skip-to-next-EMIT (well-founded on `Acc _<_ (μ'Sys (toSys r))`):
-- walk the concrete divergence chain over finitely many peer-sils to the next
-- medium/io EMIT, returning its abstract τ (into `radec r′`) + the residual chain
skipToProd : (r : RState) → Diverges (rdec r) → Acc _<_ (μ'Sys (toSys r))
  → Σ[ r′ ∈ RState ] (radec r ─[ τ ]─► radec r′) × Diverges (rdec r′)
skipToProd r d (acc rs) with otau-class r (Diverges.step d)
... | cemit r′ Meq astep = r′ , astep , subst Diverges Meq (Diverges.rest d)
... | cskip r′ Meq absEq μ↓
    with skipToProd r′ (subst Diverges Meq (Diverges.rest d)) (rs μ↓)
...   | r″ , astep′ , div″ =
        r″ , subst (λ z → z ─[ τ ]─► radec r″) (sym absEq) astep′ , div″

-- COINDUCTIVE, GUARDED forward-divergence engine: at each step skip to the next
-- EMIT, emit its abstract τ (`.step`), and corecurse (`.rest`) — the emitted τ
-- guards the corecursive call
divChainF : (r : RState) → Diverges (rdec r) → Diverges (radec r)
divChainF r d .Diverges.next =
  radec (proj₁ (skipToProd r d (<-wellFounded (μ'Sys (toSys r)))))
divChainF r d .Diverges.step =
  proj₁ (proj₂ (skipToProd r d (<-wellFounded (μ'Sys (toSys r)))))
divChainF r d .Diverges.rest =
  divChainF (proj₁ (skipToProd r d (<-wellFounded (μ'Sys (toSys r)))))
            (proj₂ (proj₂ (skipToProd r d (<-wellFounded (μ'Sys (toSys r))))))

-- the FORWARD divergence transfer
odiv→-impl : (r : RState) → Diverges (rdec r) → Diverges (radec r)
odiv→-impl r d = divChainF r d

------------------------------------------------------------------------
-- R2 D3 (THE CLOSE) — assemble the eight-field `StepOracle` and derive the
-- headline `sysBisim : systemBroken ≈DR abstractSystem`.
------------------------------------------------------------------------

-- the total step oracle: all eight per-class co-move fields
theOracle : StepOracle
theOracle .otau   = otau-impl
theOracle .oev    = oev-impl
theOracle .osqrt  = osqrt-impl
theOracle .otauB  = otauB-impl
theOracle .oevB   = oevB-impl
theOracle .osqrtB = osqrtB-impl
theOracle .odiv→  = odiv→-impl
theOracle .odiv←  = odiv←-impl

-- HEADLINE: `systemBroken ≈DR abstractSystem`
sysBisim : systemBroken blkA ≈DR abstractSystem
sysBisim = sysBisim-from theOracle

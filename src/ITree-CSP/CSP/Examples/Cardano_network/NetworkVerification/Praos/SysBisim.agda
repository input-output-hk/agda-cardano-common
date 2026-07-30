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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Process_Trees using (PTree; ExtI)

module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysBisim where

------------------------------------------------------------------------
-- The concrete model, the two endpoints, and the shared alphabet.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

-- Net_Api operators (the whole-system alphabet), to state the inner-step probe
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

-- the whole-system process type (shared with `⟦_⟧` / `absDec` / the endpoints)
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the R1 concrete decode + its home equality (`⟦ initial ⟧ ≡ systemBroken`)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode
  using ( SysState; med; nA; nB; nC; nD; ⟦_⟧; initial; dec-init )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBroken
  using ( systemBroken )
-- the R2 abstract target + its home equality (`absDec initial ≡ abstractSystem`)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.AbstractSystem
  using ( abstractSystem )

-- the shared medium decode (the left operand of `⟦_⟧` / `absDec`)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium
  using ( decMed )
-- the whole generic step/reflection machinery (R2 Task 4)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep
  using ( absDec; absDec-init; nodesOf; absNodesOf
        ; ReflOut; reflect-⟦⟧-τ; reflect-absDec-τ
        ; InnerτR; reflect-inner-τ
        ; TopEvR; reflect-top-ev
        ; IoOffers; μ
        -- the operand-generic whole-system step-intro seals (the reflect-half's
        -- assembly of a concrete `⟦ s ⟧`/`absDec s` step from a leaf step)
        ; lift-nodes-whole-τ; lift-med-whole-τ; lift-io-sync-whole-τ
        ; lift-nodes-whole-ev; lift-med-whole-ev )
-- the R2 D1 reachable-config foundation (RState subtype + decoded transition
-- `_↝_` + reachable closure `rclose`) — the domain the compositional bisim walks
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach
  using ( RState; toSys; rdec; radec; rinit; rclose; rclose-abs
        ; _↝_; mkStep; Reachable; rStep; reach; mkR )
-- the R2 D3 top-level co-moves + impossible-event refutations (visible classes)
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysRoute as SR
-- the api-class witness constructors (`IsApiCSBF`), for the `oev` api dispatch
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle as SO
-- the io / event alphabet constructors (for the `oev` label dispatch)
open import CSP.Examples.Cardano_network.Net p
  using ( apiCS; apiBF; apiKA; apiTS; apiLN; apiLF
        ; break; done; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )

-- the LTS + weak-bisim vocabulary
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; τ; evl; evLabel; Event√; √; Diverges )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF )
open WSimF
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( DRbisim; _≈DR_ )
open DRbisim

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
syswire : ⟦ initial ⟧ ≈DR absDec initial → systemBroken ≈DR abstractSystem
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
    oev   : (r : RState) {l : Event√ (⊤ {0ℓ})} {M : NetProc} → rdec r ─[ ev l ]─► M
          → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ ev l ]═► radec r′))
    otauB : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
          → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ τ ]═► rdec r′))
    oevB  : (r : RState) {l : Event√ (⊤ {0ℓ})} {M : NetProc} → radec r ─[ ev l ]─► M
          → Σ[ r′ ∈ RState ] ((M ≡ radec r′) × (rdec r ═[ ev l ]═► rdec r′))
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
bisim′-from o r .fwd .on-ev  step with o .oev r step
... | r′ , refl , wm = radec r′ , wm , bisim′-from o r′
-- backward: abstract steps reflected via `otauB`/`oevB`, residual = SWAPPED walker
bisim′-from o r .bwd .on-tau step with o .otauB r step
... | r′ , refl , wm = rdec r′ , wm , bisim′ˢ-from o r′
bisim′-from o r .bwd .on-ev  step with o .oevB r step
... | r′ , refl , wm = rdec r′ , wm , bisim′ˢ-from o r′
bisim′-from o r .div→ d = o .odiv→ r d
bisim′-from o r .div← d = o .odiv← r d
-- swapped orientation (abstract on the left): mirrors the above with the
-- concrete/abstract oracle components exchanged
bisim′ˢ-from o r .fwd .on-tau step with o .otauB r step
... | r′ , refl , wm = rdec r′ , wm , bisim′ˢ-from o r′
bisim′ˢ-from o r .fwd .on-ev  step with o .oevB r step
... | r′ , refl , wm = rdec r′ , wm , bisim′ˢ-from o r′
bisim′ˢ-from o r .bwd .on-tau step with o .otau r step
... | r′ , refl , wm = radec r′ , wm , bisim′-from o r′
bisim′ˢ-from o r .bwd .on-ev  step with o .oev r step
... | r′ , refl , wm = radec r′ , wm , bisim′-from o r′
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
sysBisim-from : StepOracle → systemBroken ≈DR abstractSystem
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

-- the TOTAL `oev` field: a visible top step reflected to its reachable successor
-- + the matching abstract weak move (impossible labels are `⊥`-eliminated)
oev-impl : (r : RState) {l : Event√ (⊤ {0ℓ})} {M : NetProc} → rdec r ─[ ev l ]─► M
  → Σ[ r′ ∈ RState ] ((M ≡ rdec r′) × (radec r ═[ ev l ]═► radec r′))
oev-impl r {√ x} step = ⊥-elim (SR.oev-no-√ (toSys r) step)
oev-impl r {evl (evLabel _ (apiCS l₀ d₀ m) a)} step = pack-oev r step (SR.top-api-comove (toSys r) SO.aicCS tt step)
oev-impl r {evl (evLabel _ (apiBF l₀ d₀ m) a)} step = pack-oev r step (SR.top-api-comove (toSys r) SO.aicBF tt step)
oev-impl r {evl (evLabel _ (done  l₀ d₀ id) a)} step = pack-oev r step (SR.top-api-comove (toSys r) SO.aicDone tt step)
oev-impl r {evl (evLabel _ (break l₀) a)} step = pack-oev r step (SR.top-break-comove (toSys r) l₀ step)
oev-impl r {evl (evLabel _ (input  l₀ d₀ id) a)} step = ⊥-elim (SR.oev-no-io (toSys r) tt step)
oev-impl r {evl (evLabel _ (output l₀ d₀ id) a)} step = ⊥-elim (SR.oev-no-io (toSys r) tt step)
oev-impl r {evl (evLabel _ (apiKA l₀ d₀ m) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-apiKA (med (toSys r))) (SR.nodes-no-nonCSBF (toSys r) tt (λ ())) step)
oev-impl r {evl (evLabel _ (apiTS l₀ d₀ m) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-apiTS (med (toSys r))) (SR.nodes-no-nonCSBF (toSys r) tt (λ ())) step)
oev-impl r {evl (evLabel _ (apiLN l₀ d₀ m) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-apiLN (med (toSys r))) (SR.nodes-no-nonCSBF (toSys r) tt (λ ())) step)
oev-impl r {evl (evLabel _ (apiLF l₀ d₀ m) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-apiLF (med (toSys r))) (SR.nodes-no-nonCSBF (toSys r) tt (λ ())) step)
oev-impl r {evl (evLabel _ (sndmsg l₀ d₀ id) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-sndmsg (med (toSys r))) (SR.nodes-no-sndmsg (toSys r)) step)
oev-impl r {evl (evLabel _ (rcvmsg l₀ d₀ id) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-rcvmsg (med (toSys r))) (SR.nodes-no-rcvmsg (toSys r)) step)
oev-impl r {evl (evLabel _ (tx     l₀ d₀ id) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-tx (med (toSys r))) (SR.nodes-no-tx (toSys r)) step)
oev-impl r {evl (evLabel _ (sndack l₀ d₀ id) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-sndack (med (toSys r))) (SR.nodes-no-sndack (toSys r)) step)
oev-impl r {evl (evLabel _ (rcvack l₀ d₀ id) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-rcvack (med (toSys r))) (SR.nodes-no-rcvack (toSys r)) step)
oev-impl r {evl (evLabel _ (ack    l₀ d₀ id) a)} step =
  ⊥-elim (SR.oev-refute (toSys r) (SR.medium-no-ack (med (toSys r))) (SR.nodes-no-ack (toSys r)) step)

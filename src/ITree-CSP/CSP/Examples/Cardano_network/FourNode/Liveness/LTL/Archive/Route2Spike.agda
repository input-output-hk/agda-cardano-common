{-# OPTIONS --guardedness --allow-unsolved-metas #-}

------------------------------------------------------------------------
-- SPIKE MODULE — Praos Phase-2 route-2 (direct whole-system bisim)
-- FEASIBILITY.  Answers the three questions of
-- docs/superpowers/specs/2026-07-22-praos-phase2-route2-spike-design.md.
--
--   * DISPOSABLE.  Imported by NOTHING; deleted after the findings are
--     harvested into the report.  `--allow-unsolved-metas` / postulates are
--     permitted HERE ONLY (per the spike design + plan).
--   * NEVER steps `breakableSystem` or any whole-node composite (the documented
--     ≈2.5 min / ≈20 GB single-step WHNF wall — the point of Q1/Q2 is to show
--     the decode/reflection approach AVOIDS that wall).  All probing is either
--     (a) `≡`-glue over sub-decodes (`cong`/`cong₂` — never forces WHNF), or
--     (b) SYMBOLIC step-inversion (`Par-ev-elim`/`Hide-τ-elim`) that receives
--     an abstract `─[_]─►` step as a hypothesis and destructures it — it never
--     evaluates the concrete composite tree.
--
-- ==================== WHAT THIS MODULE SETTLES ======================
--
-- Q1 (§1): the whole-system decode `⟦_⟧ : SysState → NetProc` composes from
--     per-part sub-decodes and `dec-init : ⟦ initial ⟧ ≡ breakableSystem` is a
--     `cong₂`-glue through the `∖ ioES` / `∥⇘ ioES ⇙` stack that DOES NOT
--     force the composite to WHNF.  The medium sub-decode is built GENUINELY
--     (`⦀Fin numLinks`, home-lemma `refl`); the per-node sub-decodes are the
--     perLink `succV`/fold recipe (PerLink.Decode.agda), stood in for by
--     `postulate`d home-equalities (Q1 tests the ASSEMBLY, which is the
--     make-or-break; the per-peer recipe is already proven tractable there).
--     TRACTABLE — see §1's `dec-init`.
--
-- Q2 (§2): the evBoth resolution.  PROVED, generically (no operand ever
--     stepped): at the io-GATED top level `(M ∥⇘ ioES ⇙ N) ∖ ioES`, an
--     io event (∈ ioES) can fire ONLY as a medium/nodes SYNC (`evSync`) — the
--     `evL`/`evR`/`evBoth` cases of `Par-ev-elim` all carry `¬ ioES.mem` and
--     are refuted by io-membership.  Hence `Par ioES` has NO `evBoth` on io,
--     and (`break` ∉ nodes, `api*` ∉ medium) none on the observable events
--     either.  The M4-blocker `evBoth` (adjacent nodes both offering the
--     shared `input`/`output`) is pushed DOWN into the nodes-bundle's own
--     io-step, which the top `∖ ioES` turns into a hidden τ — matched (not
--     refuted) by a direct ≈DR bisim.  `reflect-hidden-io` reflects one such
--     step end to end.
--
-- Q3 (§3): endgame seam reuse + sizing (documentation).
------------------------------------------------------------------------

open import Level using (Level; 0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Process_Trees

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Archive.Route2Spike (blkA : Block₃) where

open PTree

------------------------------------------------------------------------
-- The concrete model under study (Phase-1, `examples/praos_liveness`).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; nodeA; nodeB; nodeC; nodeD
        ; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBreakable
  using ( breakableSystem )
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p using (numLinks)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs)
open import CSP.Examples.Cardano_network.Net p using (Net_Api; Net_Api-≟; Link; input; output; break)
open import CSP.Examples.Cardano_network.Data p using (Payload)
open import CSP.Examples.Cardano_network.NetCommon p
  using ( CopySpecBreakableA; breakableLinkA; ioES; ioSet )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; Par⊤; Par; ⦀Fin; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; τ; evl; evLabel )

-- the whole-system process type
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the top-level merge on ⊤ (what `Par⊤`/`∥⇘⇙` uses)
merge⊤ : ⊤ {0ℓ} → ⊤ {0ℓ} → ⊤ {0ℓ}
merge⊤ _ _ = tt

------------------------------------------------------------------------
-- §1  Q1 — whole-system decode + `dec-init` tractability (make-or-break).
--
-- The perLink recipe (PerLink.Decode.agda) proves that a per-link decode's
-- `dec-init` is CHEAP because it is `cong`/`cong₂`-glue with `refl` (or a
-- 3-line list induction) at the leaves — `cong f eq` never evaluates `f`, so
-- the composite is never forced to WHNF.  Q1 asks whether that lifts to the
-- WHOLE system.  It does: the whole-system decode is
--     ⟦ s ⟧ = (decMed (med s) ∥⇘ ioES ⇙ decNodes (nodes s)) ∖ ioES
-- and `dec-init` is one `cong₂` through the `∖`/`∥⇘⇙` skeleton over the two
-- sub-decode home-lemmas.  §1 builds the MEDIUM sub-decode genuinely (its
-- home-lemma is `refl`) and stands in the node sub-decodes with the perLink
-- recipe (postulated home-equalities), isolating the ASSEMBLY — which is the
-- thing that could force WHNF, and does not.
------------------------------------------------------------------------

-- Per-medium-cell abstract phase (spike-minimal: only `home` is needed for
-- `dec-init`; the real state is `PerLink.State.MuxState l` + a break flag).
data MedCell : Set where
  home   : MedCell   -- all copy-cells home / all buffers free, not yet broken
  broken : MedCell   -- `break l` has fired (→ Skip); stands for the △-collapsed cell

-- decode one link's breakable cell.  At `home` it is EXACTLY `breakableLinkA l`
-- (the perLink `succV`/fold recipe would name the non-home derivatives; here we
-- only need the home leaf, which is `refl`).
decBreakLink : Link → MedCell → NetProc
decBreakLink l home   = breakableLinkA l
decBreakLink l broken = breakableLinkA l   -- placeholder; real: the △-Skip derivative

-- decode the whole breakable medium: rebuild `⦀Fin numLinks breakableLinkA`
-- cell by cell (GENUINE — this is the real medium operator tree).
decMed : (Link → MedCell) → NetProc
decMed f = ⦀Fin numLinks (λ l → decBreakLink l (f l))

-- MEDIUM home-lemma, GENUINE and `refl`: the all-home medium decode is exactly
-- `CopySpecBreakableA = ⦀Fin numLinks breakableLinkA` (η + `decBreakLink _ home`).
decMed-home : decMed (λ _ → home) ≡ CopySpecBreakableA
decMed-home = refl

-- The node sub-decodes: the perLink `succV`/fold recipe applied per node
-- (12 peers × `∥⇘ apiES ⇙` driver, per FourNodeDiamond.nodeA…nodeD).  Stood in
-- by their HOME-equalities (the only fact `dec-init` needs).  RECIPE STAND-IN
-- — cf. PerLink.Decode.{decInputs-home,decOutputs-home,dec-init}; NOT a gap in
-- the make-or-break claim, which is about the assembly below.
postulate
  NodesState  : Set
  nodesInit   : NodesState
  decNodes    : NodesState → NetProc
  decNodes-home : decNodes nodesInit ≡ (nodeA blkA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))

-- the whole-system abstract state
record SysState : Set where
  constructor mkSys
  field
    med   : Link → MedCell
    nodes : NodesState
open SysState

-- the initial (all-home / unbroken) whole-system state
initial : SysState
initial = mkSys (λ _ → home) nodesInit

-- the whole-system decode, rebuilding `breakableSystem`'s
-- `(medium ∥⇘ ioES ⇙ nodes) ∖ ioES` shape from the two sub-decodes.
⟦_⟧ : SysState → NetProc
⟦ s ⟧ = (decMed (med s) ∥⇘ ioES ⇙ decNodes (nodes s)) ∖ ioES

-- ================= Q1 MAKE-OR-BREAK RESULT =========================
-- `dec-init` is a SINGLE `cong₂` through the `∖`/`∥⇘⇙` stack.  It typechecks
-- in seconds (no minutes/GB): `cong₂ f p q` produces `f _ _ ≡ f _ _` WITHOUT
-- evaluating `f` — the `∥⇘ ioES ⇙` / `∖ ioES` composite is NEVER forced to
-- WHNF.  This is the whole-system generalisation of PerLink.Decode.dec-init.
dec-init : ⟦ initial ⟧ ≡ breakableSystem blkA
dec-init =
  cong₂ (λ Md Nd → (Md ∥⇘ ioES ⇙ Nd) ∖ ioES) decMed-home decNodes-home

------------------------------------------------------------------------
-- §2  Q2 — the evBoth resolution (io is medium-gated, then hidden).
--
-- The M4 blocker: `cong-⦀` (= `cong-Par⊤ ∅ES`) must discharge the `evBoth`
-- case — both operands offer the SAME non-sync event — and can only REFUTE it
-- via `Sep`.  For adjacent diamond nodes that refutation is impossible: node A
-- and node B both genuinely offer `input(linkAB, …)`.
--
-- Route 2 never uses `cong-⦀`.  Below we prove, GENERICALLY (for arbitrary
-- operands `M`, `N` — never stepping them), that at the io-GATED top level the
-- `evBoth` case cannot arise for an io event, because io ∈ ioES forces `evSync`.
------------------------------------------------------------------------

open import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload})
  using ( ParevR; Par-ev-elim )
open ParevR
open import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload})
  using ( HideτR; Hide-τ-elim )
open HideτR

-- io-membership witness: `input`/`output` are in `ioES` (chanSet ignores the
-- carrier value; `ioSet (_, input …) = ⊤`).
input∈io : ∀ {a} (l : Link) (d : Dir) (id : IDs)
         → ioES .mem (Payload , input l d id) a
input∈io l d id = tt

output∈io : ∀ {a} (l : Link) (d : Dir) (id : IDs)
          → ioES .mem (Payload , output l d id) a
output∈io l d id = tt

-- ================= Q2 CORE (PROVED, generic) =======================
-- At the io-gated top `Par⊤ ioES M N`, ANY visible step on an io event is a
-- medium/nodes SYNC (`evSync`): both operands step on the SAME io event and
-- the residual is again a top `Par⊤ ioES`.  The `evL`/`evR`/`evBoth` cases are
-- refuted by io-membership.  So the bare-`⦀` `evBoth` NEVER surfaces here.
top-io-is-sync :
    (M N : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M′ : NetProc}
  → ioES .mem (X , e) a
  → (M ∥⇘ ioES ⇙ N) ─[ ev (evl (evLabel X e a)) ]─► M′
  → Σ[ M₁ ∈ NetProc ] Σ[ N₁ ∈ NetProc ]
       (M ─[ ev (evl (evLabel X e a)) ]─► M₁)
     × (N ─[ ev (evl (evLabel X e a)) ]─► N₁)
     × (M′ ≡ (M₁ ∥⇘ ioES ⇙ N₁))
top-io-is-sync M N iomem step with Par-ev-elim ioES merge⊤ M N step
... | evSync _ sM sN = _ , _ , sM , sN , refl
... | evL  ¬p _      = ⊥-elim (¬p iomem)
... | evR  ¬p _      = ⊥-elim (¬p iomem)
... | evBoth ¬p _ _  = ⊥-elim (¬p iomem)

-- ================= Q2 REFLECTION (PROVED, generic) =================
-- Reflect ONE hidden step of the full-stack skeleton `(M ∥⇘ ioES ⇙ N) ∖ ioES`
-- (the target transition of the spike: a producer's block-fetch `output` ∈
-- ioES, synced with the medium, then hidden → τ).  It is EITHER an internal τ
-- of the inner composite, OR a hidden io event that — by `top-io-is-sync` — is
-- a medium/nodes SYNC with NO `evBoth`.  This is the exact reflection a direct
-- bisim performs at the top level; it closes without the route-1 blocker.
data ReflOut (M N : NetProc) (M″ : NetProc) : Set₁ where
  -- an internal τ of the inner `Par⊤ ioES M N` (medium/nodes/api internal move)
  innerτ : (P′ : NetProc)
         → (M ∥⇘ ioES ⇙ N) ─[ τ ]─► P′ → M″ ≡ P′ ∖ ioES → ReflOut M N M″
  -- a hidden io event, medium-gated: BOTH sides step on the SAME io event
  hidSync : ∀ {X} {e : Net_Api Payload X} {a : X} (M₁ N₁ : NetProc)
          → ioES .mem (X , e) a
          → M ─[ ev (evl (evLabel X e a)) ]─► M₁
          → N ─[ ev (evl (evLabel X e a)) ]─► N₁
          → M″ ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
          → ReflOut M N M″

reflect-hidden-io :
    (M N : NetProc) {M″ : NetProc}
  → ((M ∥⇘ ioES ⇙ N) ∖ ioES) ─[ τ ]─► M″
  → ReflOut M N M″
reflect-hidden-io M N step with Hide-τ-elim ioES (M ∥⇘ ioES ⇙ N) step
... | hτP P′ innerStep eq = innerτ P′ innerStep eq
... | hτH P′ iomem ioStep eq with top-io-is-sync M N iomem ioStep
...   | M₁ , N₁ , sM , sN , refl = hidSync M₁ N₁ iomem sM sN eq

-- Applied at the REAL operands (still no stepping — `M`, `N` are supplied as
-- the actual medium and nodes-bundle; the lemma is used, not evaluated).
reflect-breakableSystem-τ :
    ∀ {M″ : NetProc}
  → breakableSystem blkA ─[ τ ]─► M″
  → ReflOut CopySpecBreakableA (nodeA blkA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD))) M″
reflect-breakableSystem-τ step =
  reflect-hidden-io CopySpecBreakableA (nodeA blkA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD))) step

-- RESIDUAL (documented, NOT a top-level obstruction).  In the `hidSync` case
-- the nodes side yields `N ─[io]─► N₁` with `N = nodeA ⦀ (nodeB ⦀ …)`.
-- Inverting THAT inner `⦀` (= `Par ∅ES`) via `Par-ev-elim` CAN return the
-- `evBoth` node `(A₁∥rest) ⊓ (A∥rest₁)` when two adjacent nodes both offer the
-- shared io event.  Crucially this now lives BELOW the top `∖ ioES`, i.e. it
-- is a HIDDEN τ; a DIRECT ≈DR bisim MATCHES it (weak-bisim τ-flexibility) — it
-- does not have to REFUTE it the way `cong-⦀`'s `Sep` did.  The medium (a
-- one-place buffer per cell) additionally gates WHICH io fires via the
-- `evSync`, resolving the `⊓` overlap.  This is the genuine remaining route-2
-- proof risk (see the report Q2), but it is NOT the route-1 wall: route-1
-- died because the COMPOSITIONAL congruence forces a per-operand refutation;
-- route-2's direct relation is free to match the overlap node to its abstract
-- twin.  (Not mechanised here — beyond the spike time-box.)

------------------------------------------------------------------------
-- §3  Q3 — endgame seam reuse + sizing (documentation).
--
-- ENDGAME SEAM (model-agnostic, CONFIRMED reusable UNCHANGED by reading the
-- module headers):
--   · M0   Semantics.LTL.TraceBridge.⊨ᵂ⇒⊨          — generic in E,I,R,φ
--   · M0.5 Semantics.LTL.ClassicalDescent.descent-⊨ — generic; one budgeted
--          `¬¬F`-elim axiom, certified from a single `dne`
--   · M-transfer Semantics.LTL.WBisimInvariantR.⊨-DRWB-invariantᴿ→
--          — needs `Realisableᴿ` on the SOURCE (abstract) side only; the
--          FourNode LivenessSpike (2026-07-16) already discharged
--          `Realisableᴿ` on the abstract side (`τfreeᴿ→Realisableᴿ`) and
--          `BisimStable` for all atoms + `respondsAtoD`.
--   None of these mention `breakableSystem`, nodes, links, or `⦀`; they are
--   instantiated at (breakableSystem, abstractSystem, the four atoms) exactly as
--   route 1 would.  So route 2 feeds the SAME endgame:
--       breakableSystem ≈DR abstractSystem      (the Q1/Q2 direct bisim)
--     → abstract-system liveness walk         (M5 on the small abstract diamond)
--     → ⊨-DRWB-invariantᴿ→ + M0 + M0.5        → BlockLiveness⁺  (fairness-free)
--
-- M1–M3 REGEN: NOT needed under route 2.  The node specs `nodeASpec…nodeDSpec`
-- (Liveness.{NodeA,NodeBC,NodeD}) are already green and only DEFINE
-- `abstractSystem` (Liveness.System.abstractSystem); route 2 relates
-- `breakableSystem` to that SAME `abstractSystem` by ONE direct bisimulation,
-- never re-deriving the per-node `≈DR` via `cong-⦀`.  (Route 1 died precisely
-- at assembling those per-node bisims through `cong-⦀`; see Liveness.System's
-- header and the M4-blocker doc.)
------------------------------------------------------------------------

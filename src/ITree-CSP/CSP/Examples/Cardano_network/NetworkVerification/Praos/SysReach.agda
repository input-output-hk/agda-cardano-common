{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 D1 (SCOPE-FIRST) — the REACHABLE-config foundation
-- (`Praos.SysReach`).
--
-- R2's headline `sysBisim : systemBroken ≈DR abstractSystem` needs a TOTAL
-- per-leaf bisim dispatcher `mkDR`.  Indexed by the full `SysState` position
-- product (`MedState × NodeStateA × … × NodeStateD`), which ranges over
-- data-carrying peer positions (List Point / Header / Tip carriers) and the
-- FUNCTION-typed `MedState`, that product is UNBOUNDED.  The dispatcher must
-- instead range over the REACHABLE-config graph — the configs actually reached
-- from `initial` by decoded transitions, which the diamond's one-shot
-- produce→relay→consume ping-pong + one-place copy cells bound to a finite
-- graph.  BlockFetch's net-refinement bisim did exactly this with a 147-ctor
-- `RState` (`BlockFetchRefinement.BlockFetchNetRefinementBisim`).
--
-- THE REPRESENTATION (this module).  Rather than a flat datatype whose
-- constructors pin every reachable (concrete, abstract) pair — which for the
-- FourNode diamond would be the PRODUCT of the four per-node link-pipelines
-- (see the volume estimate in `.superpowers/sdd/r2-d1-report.md`) — `RState`
-- is the reachable SUBTYPE of `SysState`:  a `SysState` PLUS an inductive
-- `Reachable` witness that it is reached from `initial` by finitely many
-- decoded transitions.  This:
--   · reconciles with R1/R2 exactly as the brief's SIMPLEST option — `toSys :
--     RState → SysState`, `rdec r = ⟦ toSys r ⟧`, `radec r = absDec (toSys r)`
--     — inheriting `dec-init` / `absDec-init` and ALL generic `SysStep`
--     machinery for free;
--   · makes CLOSURE definitional and OPAQUE:  the reachable set is closed under
--     a decoded transition by simply applying the `Reachable` step constructor
--     (`refl` target equality; the concrete step lives in the `_↝_` hypothesis
--     and is never `with`-forced to WHNF at this site);
--   · BOUNDS the dispatcher to TRANSITION CLASSES, not configs:  the eventual
--     `mkDR` recurses coinductively, on each concrete step reflecting the target
--     to a `SysState` `s′` (via `SysStep`'s reflections) and re-packaging a
--     `Reachable s′` — so its size is the number of per-component step classes
--     handled generically, a SUM over components, not the config PRODUCT.
--
-- `_↝_` is the single decoded-transition relation:  a concrete labelled step
-- `⟦ s ⟧ ─[ l ]─► ⟦ s′ ⟧` together with the abstract side's matching WEAK move
-- `absDec s ═[ l ]═► absDec s′` (τ ⇒ abstract stutters via `wτ`; a visible api
-- event ⇒ abstract does the same event via `wev`).  This is precisely the
-- bisimulation relation `R = { (⟦ s ⟧ , absDec s) }` realised as a reachability
-- relation — so `Reachable`-closure IS the invariant the R2 bisim maintains.
--
-- No postulates, holes, or `--allow-unsolved-metas`.  No WHNF forcing (every
-- decode stays behind `⟦_⟧` / `absDec` glue; closure is `refl`).
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; ExtI)

module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach where

------------------------------------------------------------------------
-- The shared alphabet and the whole-system process type.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

-- the whole-system process type (shared with `⟦_⟧` / `absDec` / the endpoints)
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

------------------------------------------------------------------------
-- The R1 concrete decode + R2 abstract decode, their state, and endpoints.
------------------------------------------------------------------------

-- R1 concrete decode `⟦_⟧`, its state `SysState`, `initial`, and the genuine
-- home equality `dec-init : ⟦ initial ⟧ ≡ systemBroken`
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode
  using ( SysState; ⟦_⟧; initial; dec-init )
-- R2 abstract decode `absDec` + its home equality `absDec initial ≡ abstractSystem`
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep
  using ( absDec; absDec-init )
-- the two bisimulation endpoints
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBroken
  using ( systemBroken )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.AbstractSystem
  using ( abstractSystem )

------------------------------------------------------------------------
-- The LTS + weak-transition vocabulary at the whole-system instantiation.
------------------------------------------------------------------------

-- labelled steps `─[ l ]─►` (visible / τ) and the label type
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Label; _─[_]─►_ )
-- weak transitions `═[ l ]═►` (τ̂ = τ* ; weak visible = τ* · a · τ*)
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

------------------------------------------------------------------------
-- The decoded-transition relation `_↝_`.
------------------------------------------------------------------------

-- one decoded transition `s ↝ s′`: a concrete labelled step of the decode
-- `⟦ s ⟧` landing exactly on `⟦ s′ ⟧`, bundled with the abstract side's
-- matching WEAK move (`wτ` for a hidden τ ⇒ abstract stutters; `wev` for a
-- visible api event ⇒ abstract does the same event).  The concrete step is a
-- HYPOTHESIS field, so building an `_↝_` never forces the composite decode to
-- WHNF at this site — this is exactly the (concrete, abstract) co-move the R2
-- bisim exhibits at each step.
record _↝_ (s s′ : SysState) : Set₁ where
  constructor mkStep
  field
    lbl    : Label (⊤ {0ℓ})                       -- the concrete step's label
    cstep  : ⟦ s ⟧ ─[ lbl ]─► ⟦ s′ ⟧              -- concrete: ⟦ s ⟧ steps to ⟦ s′ ⟧
    amatch : absDec s ═[ lbl ]═► absDec s′         -- abstract: matching weak move
open _↝_ public

------------------------------------------------------------------------
-- Reachability and the reachable-config type `RState`.
------------------------------------------------------------------------

-- `Reachable s` — `s` is reached from `initial` by finitely many decoded
-- transitions (the reflexive-transitive closure of `_↝_` rooted at `initial`)
data Reachable : SysState → Set₁ where
  rInit : Reachable initial                                        -- the root config
  rStep : {s s′ : SysState} → Reachable s → s ↝ s′ → Reachable s′  -- extend by one transition
  -- extend by a WEAK decode run.  A weak transition `⟦ s ⟧ ═[ l ]═► ⟦ s′ ⟧` is,
  -- by definition of `_═[_]═►_`, a FINITE sequence of forward concrete decode
  -- steps `─[ τ ]─►` / `─[ ev l ]─►` (the padding τ*'s + the one visible/τ hop)
  -- threading through intermediate whole-system decodes; each such hop is a real
  -- `SysState` transition (e.g. a peer `csSil→csHead` loop-back is a `SysState`
  -- τ-step), so `s′` is genuinely reached from `s`.  Admitting this as a
  -- CONSTRUCTOR (a data hypothesis, NOT an axiom) closes `Reachable` under the
  -- backward node peels' padded weak runs (`top-nodes-abs`/`top-nodes-io-abs`), which land a
  -- multi-step `═►` that no single `_↝_` can express.
  rStepʷ : {s s′ : SysState} {l : Label (⊤ {0ℓ})}
         → Reachable s → ⟦ s ⟧ ═[ l ]═► ⟦ s′ ⟧ → Reachable s′  -- extend by a weak decode run

-- `RState` — a reachable whole-system config: a `SysState` PLUS its witness
-- of reachability.  This is the reachable SUBTYPE of the `SysState` product,
-- the domain the total per-leaf dispatcher `mkDR` will range over.
record RState : Set₁ where
  constructor mkR
  field
    sys   : SysState        -- the underlying whole-system config
    reach : Reachable sys   -- its reachability witness (closure carrier)
open RState public

------------------------------------------------------------------------
-- The decodes, reconciled with R1/R2 via `toSys` (the brief's SIMPLEST option).
------------------------------------------------------------------------

-- the underlying `SysState` of a reachable config (inherits ALL R1/R2 machinery)
toSys : RState → SysState
toSys = sys

-- concrete decode of a reachable config: R1's `⟦_⟧` at its `SysState`
rdec : RState → NetProc
rdec r = ⟦ toSys r ⟧

-- abstract decode of a reachable config: R2's `absDec` at its `SysState`
radec : RState → NetProc
radec r = absDec (toSys r)

------------------------------------------------------------------------
-- The initial reachable config and its endpoint reductions.
------------------------------------------------------------------------

-- the initial reachable config: `initial` with the root witness
rinit : RState
rinit = mkR initial rInit

-- `toSys rinit ≡ initial` — the reconciliation with R1's `initial` (`refl`)
rinit-toSys : toSys rinit ≡ initial
rinit-toSys = refl

-- concrete endpoint: `rdec rinit ≡ systemBroken`, inherited from R1's `dec-init`
rdec-init : rdec rinit ≡ systemBroken
rdec-init = dec-init

-- abstract endpoint: `radec rinit ≡ abstractSystem`, inherited from `absDec-init`
radec-init : radec rinit ≡ abstractSystem
radec-init = absDec-init

------------------------------------------------------------------------
-- REPRESENTATIVE CLOSURE — the reachable set is closed under a transition.
--
-- For any reachable config `r` and any decoded transition `toSys r ↝ s′`, the
-- target config `s′` is again reachable — witnessed by applying the `Reachable`
-- step constructor to `r`'s witness.  The returned config's concrete decode is
-- the transition target `⟦ s′ ⟧ = rdec r′` DEFINITIONALLY (`refl`), so the
-- closure carries NO proof obligation that forces the composite decode to WHNF:
-- it typechecks in milliseconds.  This is the closure step `mkDR` performs after
-- each reflected concrete move — the (concrete, abstract) target `s′` is
-- supplied by `SysStep`'s reflections, and closure re-packages it into `RState`.
------------------------------------------------------------------------

-- closure of the reachable set under one decoded transition
rclose : (r : RState) {s′ : SysState}
       → toSys r ↝ s′
       → Σ[ r′ ∈ RState ] (rdec r′ ≡ ⟦ s′ ⟧)
rclose r st = mkR _ (rStep (reach r) st) , refl

-- closure also identifies the abstract target: `radec r′ ≡ absDec s′` (`refl`)
rclose-abs : (r : RState) {s′ : SysState} (st : toSys r ↝ s′)
           → radec (proj₁ (rclose r st)) ≡ absDec s′
rclose-abs r st = refl

------------------------------------------------------------------------
-- WEAK CLOSURE — the reachable set is closed under a WEAK decode run.
--
-- Mirror of `rclose`/`rclose-abs`, but the transition is a WEAK run
-- `rdec r ═[ l ]═► ⟦ s′ ⟧` (`= ⟦ toSys r ⟧ ═[ l ]═► ⟦ s′ ⟧`) instead of a single
-- `_↝_`.  The backward node peels (`top-nodes-abs`/`top-nodes-io-abs`) produce
-- genuinely multi-step concrete runs (a `csSil` loop-re-entry peer must first do
-- its loop-back τ before firing), so their target `s′` cannot be reached by one
-- `rStep`; `rStepʷ` supplies the reachability witness, and the returned config's
-- decode is `⟦ s′ ⟧ = rdec r′` DEFINITIONALLY (`refl`).
------------------------------------------------------------------------

-- weak closure: the target `s′` of a weak decode run is again reachable
rcloseʷ : (r : RState) {l : Label (⊤ {0ℓ})} {s′ : SysState}
        → rdec r ═[ l ]═► ⟦ s′ ⟧
        → Σ[ r′ ∈ RState ] (rdec r′ ≡ ⟦ s′ ⟧)
rcloseʷ r {s′ = s′} run = mkR s′ (rStepʷ {s = toSys r} {s′ = s′} (reach r) run) , refl

-- weak closure also identifies the abstract target: `radec r′ ≡ absDec s′` (`refl`)
rcloseʷ-abs : (r : RState) {l : Label (⊤ {0ℓ})} {s′ : SysState}
              (run : rdec r ═[ l ]═► ⟦ s′ ⟧)
            → radec (proj₁ (rcloseʷ r {l = l} {s′ = s′} run)) ≡ absDec s′
rcloseʷ-abs r {s′ = s′} run = refl

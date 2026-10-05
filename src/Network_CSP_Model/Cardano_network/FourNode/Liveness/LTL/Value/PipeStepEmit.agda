{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the FINE-STEP `StepEmit` FOLD ENGINE
-- (`Praos.PipeStepEmit`).
--
-- SESSION-16 (upd 48) established that a walk step is a WEAK visible move
-- `radec r ═[ ev (evl e) ]═► t′ = wev (τ*) (visible) (τ*)`, and that the
-- invariant-relevant granularity is the FINE (per-τ / single-visible) step, NOT
-- the whole weak move: a single weak move bundles many hidden-io hand-offs plus
-- one visible driver step, and `PipeStep⁺` was extended with the catch-all
-- carrier `psWeak : (PipeInv⁺ l s → PipeInv⁺ l s′) → PipeStep⁺ l s s′` precisely
-- so that a FOLDED per-fine-step preservation map can be handed to
-- `pipeInv⁺-step`.
--
-- THIS module is the light structural ENGINE that performs that fold.  It
-- mirrors `WalkStepLift.liftReach-ev` / `PipeReportGen.liftτ*-gen′`: decompose
-- `wev pre mid post`, fold a per-τ preservation combinator (`TauStep`) across
-- the two τ-runs, apply a visible-middle preservation combinator (`EvStep`) to
-- the strong hop, and compose the three preservation maps into ONE
-- `PipeInv⁺ l (toSys r) → PipeInv⁺ l (toSys r′)`, wrapped by `psWeak`.  The
-- result matches `PipeExpose.StepEmit l` EXACTLY.
--
-- The two per-fine-step combinators isolate the remaining discharge work:
--   · `TauStep l` — each hidden τ hop preserves `PipeInv⁺`.  Its MEDIUM-τ half
--     (`τpreserve-med`, drain-to-empty) is discharged HERE (light, no cone) via
--     the `PipeIoHandoff` `pipeInv⁺-{up,dn}-empty` cores; its io-SYNC half needs
--     `FillSource` (the server-output io-source) plus a per-node client-fixity
--     cone (PipeNodeFix-scale), left as the reported gap.
--   · `EvStep l` — the visible api-CSBF middle driver step.  Needs the CONCRETE
--     driver transition (`pipeInv⁺-prod-send`/`-relay-fwd`/receive/move cores);
--     the existing PERMISSIVE `adv-of` classifiers carry no monotone map, so this
--     is the reported driver-dispatch gap.
--
-- `FillSource l` is defined here as the isolated server-output⇒sent/fwd source
-- fact each io FILL needs.  No postulate/hole/meta.  Base modules READ-ONLY.
--
-- SESSION-28.  `FillSource` was FALSE as originally stated, because its
-- antecedent was mere cell NON-EMPTINESS: node A's BF server fills the very
-- same cell with `MsgStartBatch` while the producer driver is still at `pp5`
-- (`Praos.PipeCellFalse` refutes it mechanically).  After `PipeInv`'s
-- payload refinement (`CellNE` ⇝ `CellHasBlk` = "the cell holds a BlockFetch
-- `MsgBlock`") the statement below is TRUE and its discharge is:
--   `PipeFillSource.blockFill-forces-srv` (a block-carrying fill pins the
--   sending BF server to `bsBlk1`) ∘ `PipeSrvInv.SrvCoupled` (server holds ⇒
--   producer sent / relay forwarded), modulo the io NODE cone extended with
--   SERVER slots so the firing peer is identified with the leg's `upSrv`/`dnSrv`
--   (`PipeFillSource.fill-up-source` / `-dn-source` are the ready bridges).
------------------------------------------------------------------------

open import Data.Product using ( Σ; Σ-syntax; _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeStepEmit (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; Event )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys; rdec )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( empty )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( PipeInv⁺; PipeStep⁺; psWeak; prodOf; relayOf; ProdSent; RelayFwd
        ; cellUp; cellDn; CellHasBlk )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeExpose blkA as PE
open PE using ( StepEmit )

------------------------------------------------------------------------
-- The two per-fine-step preservation combinators.  Each reflects ONE fine
-- transition of the weak move to its reachable successor `r′` and the
-- `PipeInv⁺`-preservation map for that single step.
------------------------------------------------------------------------

-- one hidden τ hop preserves `PipeInv⁺` (medium-τ drain, or io-sync fill/drain)
TauStep : TwoLegs → Set₁
TauStep l = (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
          → Σ[ r′ ∈ RState ]
              (M ≡ radec r′) × (PipeInv⁺ l (toSys r) → PipeInv⁺ l (toSys r′))

-- one strong visible hop preserves `PipeInv⁺` (the api-CSBF driver step / break)
EvStep : TwoLegs → Set₁
EvStep l = (r : RState) {e : Event} {M : NetProc} → radec r ─[ ev (evl e) ]─► M
         → Σ[ r′ ∈ RState ]
             (M ≡ radec r′) × (PipeInv⁺ l (toSys r) → PipeInv⁺ l (toSys r′))

------------------------------------------------------------------------
-- The FILL io-source combinator `FillSource l`: the isolated node-FSM fact each
-- cell FILL needs, in the exact shape a `TauStep` io reflector consumes.  Over a
-- HIDDEN io-run `rdec r ═[ τ ]═► ⟦ s′ ⟧` the three leg drivers are τ-STABLE
-- (they move only on visible api steps), so `prodOf l (toSys r) ≡ prodOf l s′`
-- etc.  A leg-`l` UPSTREAM cell that was `empty` at `r` and is NON-empty at the
-- io-successor `s′` was FILLED (`empty → full` via node-A's BF server output),
-- which fires only AFTER `sendBFBlock` — so the producer had already SENT at `r`
-- (`ProdSent (prodOf l (toSys r))`).  Symmetrically a downstream fill forces
-- `RelayFwd (relayOf l (toSys r))`.  This is the genuine, SATISFIABLE server-FSM
-- statement (NOT the false unconditional claim): its antecedents pin the fill to
-- a real hidden-io successor of `r` and to leg-`l`'s own cell going empty→full.
------------------------------------------------------------------------

-- the two server-output source facts a leg-`l` fill needs, at a hidden-io
-- successor `s′` of the reachable `r`
FillSource : TwoLegs → Set₁
FillSource l = (r : RState) (s′ : SysState)
             → rdec r ═[ τ ]═► ⟦ s′ ⟧
             → (cellUp l (toSys r) ≡ empty → CellHasBlk (cellUp l s′)
                  → ProdSent (prodOf  l (toSys r)))   -- upstream fill  ⇐ producer sent
             × (cellDn l (toSys r) ≡ empty → CellHasBlk (cellDn l s′)
                  → RelayFwd (relayOf l (toSys r)))   -- downstream fill ⇐ relay forwarded

------------------------------------------------------------------------
-- The ENGINE (light structural fold).  Mirror `WalkStepLift.liftReach-ev`
-- STRENGTHENED to thread a preservation map: fold `TauStep` over the leading
-- τ-run, apply `EvStep` to the visible middle, fold `TauStep` over the trailing
-- τ-run, compose the three preservations left-to-right, and hand the result to
-- `psWeak`.  Matches `StepEmit l` exactly.
------------------------------------------------------------------------

module _ (l : TwoLegs) where

  -- fold `TauStep` across a hidden τ-run, threading the composed preservation
  -- (generalised over the start tree with a `start ≡ radec r` witness so the
  -- Star sub-term recurses structurally, exactly as `WalkStepLift.liftτ*′`)
  liftτ*-preserve′ : TauStep l → (r : RState) {start u : NetProc}
                   → start ≡ radec r → start ─[τ*]─► u
                   → Σ[ r′ ∈ RState ]
                       (u ≡ radec r′) × (PipeInv⁺ l (toSys r) → PipeInv⁺ l (toSys r′))
  liftτ*-preserve′ ts r eq τ*-refl = r , eq , (λ x → x)
  liftτ*-preserve′ ts r eq (τ*-step s rest)
    with ts r (subst (λ z → z ─[ τ ]─► _) eq s)
  ... | r₁ , eq₁ , p₁ with liftτ*-preserve′ ts r₁ eq₁ rest
  ...   | r′ , equ , p′ = r′ , equ , (λ x → p′ (p₁ x))

  -- the fine-step fold: decompose `wev pre mid post`, fold the τ-runs, dispatch
  -- the middle, compose, wrap `psWeak`
  stepEmitFrom : TauStep l → EvStep l → StepEmit l
  stepEmitFrom ts es r (wev pre mid post)
    with liftτ*-preserve′ ts r refl pre
  ... | r₁ , eq₁ , p₁
      with es r₁ (subst (λ z → z ─[ ev (evl _) ]─► _) eq₁ mid)
  ...   | r₂ , eq₂ , p₂
        with liftτ*-preserve′ ts r₂ refl (subst (λ z → z ─[τ*]─► _) eq₂ post)
  ...     | r′ , equ , p₃ =
            r′ , equ , psWeak (λ x → p₃ (p₂ (p₁ x)))

  ------------------------------------------------------------------------
  -- DELIVERABLE (2): `pipeInv⁺` DERIVED ALONG THE WALK via the fold engine.
  -- Instantiating `PipeExpose.pipeInv⁺-along-walk` (the green fold of
  -- `pipeInv⁺-step` over the located `producedA` walk) at `stepEmitFrom ts es`
  -- delivers `PipeInv⁺ l (toSys r′)` at the frame — modulo the two per-step
  -- combinators `ts`/`es` (whose discharge is the remaining work: io `TauStep`
  -- needs `FillSource`, the visible-middle `EvStep` needs the driver dispatch).
  -- Return type inferred from `pipeInv⁺-along-walk` (avoids re-spelling the
  -- `WTrace`/`producedA` frame type here).
  ------------------------------------------------------------------------

  pipeInv⁺-along-walk-from : (b : Block₃) → TauStep l → EvStep l → _
  pipeInv⁺-along-walk-from b ts es = PE.pipeInv⁺-along-walk b l (stepEmitFrom ts es)

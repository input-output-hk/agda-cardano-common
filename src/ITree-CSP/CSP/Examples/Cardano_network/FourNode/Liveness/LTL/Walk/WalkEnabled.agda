{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 (FRONTIER-A) — the WEnabled event-class the `wprog`
-- premise quantifies over (`IntactApiClass`) + the REFUTATION that lets
-- `deliver`'s done/stuck/√ (terminal) frames be discharged
-- (`Praos.WalkEnabled`).
--
-- SCOPE VERDICT: PATH (i) — a WEAK STABILITY argument, NO τ*-confluence.
-- The subtlety prior sessions glossed: `WEnabled C (radec r)` (a weak
-- visible step OUT OF `radec r`) does NOT by itself refute a `done`/`stuck`
-- frame, because those frames observe a τ*-DESCENDANT `u` of `radec r`
-- (`radec r ─[τ*]─► u`, `force u ≡ ret` / `IsStuck u`), not `radec r`
-- itself; and a react "sliding" node can offer a visible event AND have a
-- τ leading to `ret` simultaneously, so `WEnabled` and a `done`-to-`ret`
-- run genuinely COEXIST on a generic tree (confluence does not help — the
-- branch is a single node).  The sound closure does NOT transport the
-- offer forward; instead it observes that `u` is again a REACHABLE PENDING
-- config, and re-invokes the ∀-quantified premise THERE:
--
--   (1) `WalkTauExpose.liftτ*-expose` (already green) turns the internal
--       τ*-run `radec r ─[τ*]─► u` into a reachable `r′` with `u ≡ radec r′`
--       AND `DFix` (nD's two D-consume phases `cons-BD`/`cons-CD` are FIXED
--       across the run) — because no abstract τ (medium-drain / hidden
--       io-sync) can fire the VISIBLE api `recvBFBlock@D`.
--   (2) `DFix` ⇒ `Pr b r′` (the pending invariant is phase-only, hence
--       preserved by the fixity) — `Pr-DFix`.
--   (3) `wprog r′ (Pr b r′) : WEnabled (IntactApiClass b) (radec r′ ≡ u)`
--       re-supplies enabledness AT the terminal descendant.
--   (4) A GENERIC, confluence-free "WEnabled at a `ret`/stuck STATE is
--       absurd" lemma (`wenabled-ret-state-⊥` / `wenabled-stuck-state-⊥`)
--       then closes: a `ret` node offers no `evl` event and no τ, and a
--       stuck state offers nothing at all, so a weak visible step out of it
--       is impossible.
--
-- The `div` frame is out of scope here (killed by `WalkConv.absNoDiv`).
--
-- LIGHT: only imports `liftτ*-expose` + the generic LTS inversions; no
-- SysOracle cone re-check.  No postulate/hole/meta.  Models READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Empty using ( ⊥ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Function using ( case_of_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI; ret; react; sil )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkEnabled (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; apiBF; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; Event√; evl; √; evLabel; ev; τ; _─[_]─►_; sRet; ev-inv; τ-inv )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev )
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( IsStuck )
open import Semantics.LTL.Fairness {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WEnabled )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( cph )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( Pr; phBD; phCD; InCp03; TwoLegs; legBD; legCD; phOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkTauExpose blkA
  using ( DFix; BD; CD; liftτ*-expose )

------------------------------------------------------------------------
-- §1  `IntactApiClass` — the WEnabled event class `wprog` quantifies over.
--
-- The intact-path BlockFetch driver events the liveness spec observes:
-- `apiBF` at `hi` on EITHER candidate intact path's links — group-1
-- {AB, BD} or group-2 {AC, CD}.  This is exactly the union of the spec's
-- `C-ABD`/`C-ACD` fetch-driver classes (`FourNodeDiamondLiveness`); the
-- carried block `b` is not read (the class is value-agnostic, mirroring the
-- spec's classes), it is threaded only to match `wprog`'s signature.  Every
-- non-`apiBF` event (crucially `apiKA` and wrong-direction/wrong-link
-- `apiBF`) falls to the catch-all `⊥`.
------------------------------------------------------------------------

IntactApiClass : Block₃ → Event → Set
IntactApiClass _ (evLabel _ (apiBF l d _) _) =
  (((l ≡ linkAB) ⊎ (l ≡ linkBD)) ⊎ ((l ≡ linkAC) ⊎ (l ≡ linkCD))) × (d ≡ hi)
IntactApiClass _ _ = ⊥

------------------------------------------------------------------------
-- §2  The GENERIC, confluence-free "WEnabled at a terminal STATE is
--     absurd" core (path-(i) stability).  Parametric in the class `C`.
------------------------------------------------------------------------

-- A `ret` node performs no weak visible (`evl`) step: its only τ*-prefix is
-- reflexive (a `ret` has no τ — `sil`/`react` both differ), and a `ret` is
-- not a `react`, so it cannot fire the `sVis` middle either.
wenabled-ret-state-⊥ : ∀ {ℓc} {C : Event → Set ℓc} {t : NetProc} {x : ⊤ {0ℓ}}
                     → PTree.force t ≡ ret x → WEnabled C t → ⊥
wenabled-ret-state-⊥ eq (evLabel A e a , _ , wev τ*-refl mid _ , _) with ev-inv mid
... | _ , _ , reacteq , _ = case trans (sym eq) reacteq of λ ()
wenabled-ret-state-⊥ eq (_ , _ , wev (τ*-step s _) _ _ , _) with τ-inv s
... | inj₁ sileq                          = case trans (sym eq) sileq   of λ ()
... | inj₂ (_ , _ , _ , _ , reacteq , _)  = case trans (sym eq) reacteq of λ ()

-- A stuck state performs NO transition at all, so certainly no weak visible
-- step: whether the weak step opens with a τ (`τ*-step`) or fires the middle
-- immediately (`τ*-refl`), `IsStuck` refutes that first transition.
wenabled-stuck-state-⊥ : ∀ {ℓc} {C : Event → Set ℓc} {t : NetProc}
                       → IsStuck t → WEnabled C t → ⊥
wenabled-stuck-state-⊥ stk (_ , _ , wev τ*-refl        mid _ , _) = stk mid
wenabled-stuck-state-⊥ stk (_ , _ , wev (τ*-step s _)  _   _ , _) = stk s

------------------------------------------------------------------------
-- §3  The deliver-facing refutations: from a PENDING reachable `r` and the
--     `wprog` premise, a `done`/`stuck`/√ terminal frame is absurd.
--
-- Each lands the internal τ*-run at a reachable pending descendant via
-- `liftτ*-expose` (+ `Pr-DFix`), re-supplies `WEnabled` there via `wprog`,
-- and closes with the §2 stability core.  This is exactly what `deliver`'s
-- `done`/`stuck`/√ branches call (after `⊥-elim`).
------------------------------------------------------------------------

module _
  (b : Block₃)
  (wprog : (r : RState) → Pr b r → WEnabled (IntactApiClass b) (radec r))
  where

  -- `Pr` is preserved by D-phase fixity (`DFix`): `Pr` tracks ONE D-consume
  -- leg, and `DFix` fixes both underlying `ConsDPh`s — so the tracked leg's
  -- `InCp03` transports back unchanged.  (Stated at the module's fixed `b` —
  -- `Pr` ignores its block argument, so a quantified `b` would be an
  -- un-pinnable implicit.)
  Pr-DFix : (r r′ : RState)
          → Pr b r → DFix (toSys r) (toSys r′) → Pr b r′
  Pr-DFix _ _ (legBD , h) (bfix , cfix) = legBD , subst InCp03 (cong cph (sym bfix)) h
  Pr-DFix _ _ (legCD , h) (bfix , cfix) = legCD , subst InCp03 (cong cph (sym cfix)) h

  -- `done`: `radec r ─[τ*]─► u` with `force u ≡ ret x` at a pending `r`.
  wenabled-done-⊥ : (r : RState) → Pr b r → {u : NetProc} {x : ⊤ {0ℓ}}
                  → radec r ─[τ*]─► u → PTree.force u ≡ ret x → ⊥
  wenabled-done-⊥ r pr {u} {x} run eq with liftτ*-expose r run
  ... | r′ , u≡ , _ , dfix =
        wenabled-ret-state-⊥ (subst (λ z → PTree.force z ≡ ret x) u≡ eq)
                             (wprog r′ (Pr-DFix r r′ pr dfix))

  -- `stuck`: `radec r ─[τ*]─► u` with `IsStuck u` at a pending `r`.
  wenabled-stuck-⊥ : (r : RState) → Pr b r → {u : NetProc}
                   → radec r ─[τ*]─► u → IsStuck u → ⊥
  wenabled-stuck-⊥ r pr {u} run stk with liftτ*-expose r run
  ... | r′ , u≡ , _ , dfix =
        wenabled-stuck-state-⊥ (subst IsStuck u≡ stk)
                               (wprog r′ (Pr-DFix r r′ pr dfix))

  -- `√`-step: `radec r ═[ ev (√ x) ]═► q` at a pending `r`.  The weak step's
  -- middle is a `sRet` (`force p′ ≡ ret x`), so its τ*-prefix reaches a `ret`
  -- descendant — same closure as `done`.
  wenabled-sqrt-⊥ : (r : RState) → Pr b r → {q : NetProc} {x : ⊤ {0ℓ}}
                  → radec r ═[ ev (√ x) ]═► q → ⊥
  wenabled-sqrt-⊥ r pr {q} {x} (wev pfx (sRet feq) _) with liftτ*-expose r pfx
  ... | r′ , p′≡ , _ , dfix =
        wenabled-ret-state-⊥ (subst (λ z → PTree.force z ≡ ret x) p′≡ feq)
                             (wprog r′ (Pr-DFix r r′ pr dfix))

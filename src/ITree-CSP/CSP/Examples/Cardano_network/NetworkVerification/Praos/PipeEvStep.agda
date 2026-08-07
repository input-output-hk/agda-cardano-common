{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the visible-middle combinator `EvStep`
-- (`Praos.PipeEvStep`).
--
-- `PipeStepEmit.stepEmitFrom` consumes an `EvStep l`: a preservation reflector
-- for the SINGLE visible hop of a weak move.  THIS module builds it.
--
-- The event `e` of a visible top step of `radec r = absDec (toSys r)` is
-- dispatched by its label (mirror of `SysBisim.oevB-impl`):
--   · api-CSBF (apiCS / apiBF / done) → the DRIVER step.  The reflect bridge
--     `reach-ev-driver` (mirror of `PipeClassRelay.reach-ev-classrelay`, but
--     using `PipeEvDriverCone.driverExpose` in place of the class cone) lands the
--     step at a reachable `r′` (`toSys r′ = s′` DEFINITIONALLY, since
--     `r′ = proj₁ (rcloseʷ …)`) with the leg-`l` `LegDriverStep`; then
--     `legStep→pres` dispatches that to the `PipeEvDriver` preservation glue.
--   · break → the medium breaks a link; every node (hence every leg driver /
--     client) is fixed, and break preserves the copy cells (`phase`) — so the
--     preservation is `pipeInv⁺-frame`.
--   · io (input/output ∈ ioES) is HIDDEN (`oevB-no-io`); the inert api events
--     (apiKA/apiTS/apiLN/apiLF) and the wire messages are impossible (refuted at
--     medium + abstract nodes via `oevB-refute`).
--
-- `evStep : EvStep l` is TOTAL (session 26): the `LegDriverStep`
-- `ldRelay`/`ldCons` constructors now CARRY the client-evolution disjunct and
-- the receive-coupling facts (`wUp`/`wDn`) — built at the cone's peel sites —
-- so `legStep→pres` is self-contained and the api case is a one-liner over
-- `reach-ev-driver`.
--
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₁ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeEvStep (blkA : Block₃) where

open import Data.Sum using ( _⊎_; inj₂ )
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Unit.Polymorphic using ( tt )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; Block₃; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; break
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; done; input; output
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( hi; N2N_BlockFetch )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks )

open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; ⦀Fin; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel; Event )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA using
  ( MedState; mkMed; phase; broken; decLink; decMed )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA using
  ( NetProc; absNodesOf; nodesOf; absDec; lift-med-whole-ev
  ; reflect-top-ev; medEv; nodesEv )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA using
  ( TwoLegs; legBD; legCD; phOf; InCp03 )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA using
  ( RState; toSys; radec; rdec; rcloseʷ; rcloseʷ-abs )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA using
  ( IsApiCSBF; aicCS; aicBF; aicDone )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA
  using ( ⦀Fin-ev-inv )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA
  using ( finUpd )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysBisim blkA using
  ( lift-nodes-whole-wev; oevB-no-io; oevB-refute )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkMeasure blkA using
  ( ConsAdv )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA using
  ( PipeInv⁺; prodOf; relayOf; cellUp; cellDn; upClient; dnClient
  ; RelayPre; RelayHas; RelayFwd; ProdSent; ConsRecv; BFcHasBlk
  ; pipeInv⁺-relay-recv; pipeInv⁺-frame
  ; pipeInv⁺-relay-move; pipeInv⁺-relay-fwd; pipeInv⁺-cons-move; pipeInv⁺-cons-recv )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeEvDriver blkA using
  ( RelayStepKind; rMove; rFwd; rRecv
  ; pipeInv⁺-relay-move′; pipeInv⁺-relay-fwd′; pres-prod; pres-cons
  ; ConsStepKind; cMove; cRecv; consadv-step )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeEvDriverCone blkA using
  ( LegDriverStep; ldProd; ldRelay; ldCons; ldFix; driverExpose )
-- SESSION-33 (G2d): the BF-server coupling and its preservation cores
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeSrvInv blkA using
  ( SrvCoupled; srvCoupled-frame; srvCoupled-pres; UpSrvEvo; DnSrvEvo
  ; padv-sent-mono; rk-fwd-mono )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeStepEmit blkA using
  ( EvStep )

------------------------------------------------------------------------
-- `pres-relay-rk`: the `RelayStepKind` analogue of `PipeEvDriver.pres-relay`.
-- The cone exposes the relay advance as a `RelayStepKind` (the `consuming cp6`
-- composite is not a single `CPAdv`), so we dispatch it directly to the primed
-- relay cores — mirror of `pres-relay`'s body after `with cpadv-step ca`.
------------------------------------------------------------------------

pres-relay-rk : (l : TwoLegs) (s s′ : SysState)
  → RelayStepKind (relayOf l s) (relayOf l s′)
  → prodOf   l s ≡ prodOf   l s′ → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → dnClient l s ≡ dnClient l s′
  → (BFcHasBlk (upClient l s′) → ⊥)
  → (RelayPre (relayOf l s) → RelayHas (relayOf l s′) → BFcHasBlk (upClient l s))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pres-relay-rk l s s′ rk pe ce cue cde de ¬blk′ wUp pinv with rk
... | rMove fP fH fF _ =
      pipeInv⁺-relay-move′ l s s′ pe ce cue cde de ¬blk′ fP fH fF pinv
... | rFwd hHas hFwd _ =
      pipeInv⁺-relay-fwd′ l s s′ pe ce cue ¬blk′ hHas hFwd pinv
... | rRecv hPre hHas =
      pipeInv⁺-relay-recv l s s′ pe ce cue cde de hPre (wUp hPre hHas) hHas pinv

------------------------------------------------------------------------
-- `pres-relay-evo` / `pres-cons-evo`: the evolution-aware relay / consumer
-- dispatchers.  The cone hands the firing leg's co-located client EVOLUTION as
-- a disjunct — client FIXED (use the full-fixity `PipeInv` move cores) or
-- fired-visibly-to-¬-block (use the primed successor-non-block cores) — plus
-- the guarded receive-coupling fact (`wUp`/`wDn`), consumed on the receive.
------------------------------------------------------------------------

pres-relay-evo : (l : TwoLegs) (s s′ : SysState)
  → RelayStepKind (relayOf l s) (relayOf l s′)
  → prodOf   l s ≡ prodOf   l s′ → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → dnClient l s ≡ dnClient l s′
  → ((upClient l s ≡ upClient l s′) ⊎ (BFcHasBlk (upClient l s′) → ⊥))
  → (RelayPre (relayOf l s) → RelayHas (relayOf l s′) → BFcHasBlk (upClient l s))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pres-relay-evo l s s′ rk pe ce cue cde de (inj₂ ¬blk′) wUp =
  pres-relay-rk l s s′ rk pe ce cue cde de ¬blk′ wUp
pres-relay-evo l s s′ rk pe ce cue cde de (inj₁ ue) wUp with rk
... | rMove fP fH fF _ = pipeInv⁺-relay-move l s s′ pe ce cue cde ue de fP fH fF
... | rFwd hHas hFwd _ = pipeInv⁺-relay-fwd l s s′ pe ce cue ue hHas hFwd
... | rRecv hPre hHas  = pipeInv⁺-relay-recv l s s′ pe ce cue cde de hPre (wUp hPre hHas) hHas

pres-cons-evo : (l : TwoLegs) (s s′ : SysState)
  → ConsAdv (phOf l s) (phOf l s′)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′
  → ((dnClient l s ≡ dnClient l s′) ⊎ (BFcHasBlk (dnClient l s′) → ⊥))
  → (InCp03 (phOf l s) → ConsRecv (phOf l s′) → BFcHasBlk (dnClient l s))
  → PipeInv⁺ l s → PipeInv⁺ l s′
pres-cons-evo l s s′ ca pe re cue cde ue (inj₂ ¬blk′) wDn =
  pres-cons l s s′ ca pe re cue cde ue ¬blk′ wDn
pres-cons-evo l s s′ ca pe re cue cde ue (inj₁ de) wDn with consadv-step ca
... | cMove fI fR _    = pipeInv⁺-cons-move l s s′ pe re cue cde ue de fI fR
... | cRecv hPre hRecv = pipeInv⁺-cons-recv l s s′ pe re cue cde ue hPre (wDn hPre hRecv) hRecv

------------------------------------------------------------------------
-- `legStep→pres`: dispatch a `LegDriverStep l s s′` to the `PipeInv⁺`
-- preservation map.  SELF-CONTAINED since the session-26 cone-witness
-- extension: `ldRelay`/`ldCons` carry the client-evolution disjunct and the
-- receive-coupling facts, so no external premise remains.
------------------------------------------------------------------------

legStep→pres : (l : TwoLegs) (s s′ : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → LegDriverStep l s s′ e a
  → PipeInv⁺ l s → PipeInv⁺ l s′
legStep→pres l s s′ (ldProd padv re ce cue cde ue de) =
  pres-prod l s s′ padv re ce cue cde ue de
legStep→pres l s s′ (ldRelay rk pe ce cue cde de upEvo wUp) =
  pres-relay-evo l s s′ rk pe ce cue cde de upEvo wUp
legStep→pres l s s′ (ldCons cadv _lbl pe re cue cde ue dnEvo wDn) =
  pres-cons-evo l s s′ cadv pe re cue cde ue dnEvo wDn
legStep→pres l s s′ (ldFix pe re ce cue cde ue de) =
  pipeInv⁺-frame l s s′ pe re ce cue cde ue de

------------------------------------------------------------------------
-- `pickLeg`: select leg `l`'s `LegDriverStep` from `driverExpose`'s pair.
------------------------------------------------------------------------

pickLeg : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
        → LegDriverStep legBD s s′ e a → LegDriverStep legCD s s′ e a
        → LegDriverStep l s s′ e a
pickLeg legBD s s′ ldBD ldCD = ldBD
pickLeg legCD s s′ ldBD ldCD = ldCD

-- SESSION-33 (G2d): the same selection for `driverExpose`'s two SERVER pairs
pickLegSrv : (l : TwoLegs) (s s′ : SysState)
           → (UpSrvEvo legBD s s′ × DnSrvEvo legBD s s′)
           → (UpSrvEvo legCD s s′ × DnSrvEvo legCD s s′)
           → UpSrvEvo l s s′ × DnSrvEvo l s s′
pickLegSrv legBD s s′ sBD sCD = sBD
pickLegSrv legCD s s′ sBD sCD = sCD

-- the two consequent-monotone maps `srvCoupled-pres` demands, read off the
-- leg's driver step (the firing driver's own advance; every other component is
-- fixed, so the map is a `subst`)
legStep→pmono : (l : TwoLegs) (s s′ : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → LegDriverStep l s s′ e a → ProdSent (prodOf l s) → ProdSent (prodOf l s′)
legStep→pmono l s s′ (ldProd padv _ _ _ _ _ _)   = padv-sent-mono padv
legStep→pmono l s s′ (ldRelay _ pe _ _ _ _ _ _)  = subst ProdSent pe
legStep→pmono l s s′ (ldCons _ _ pe _ _ _ _ _ _) = subst ProdSent pe
legStep→pmono l s s′ (ldFix pe _ _ _ _ _ _)      = subst ProdSent pe

legStep→rmono : (l : TwoLegs) (s s′ : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → LegDriverStep l s s′ e a → RelayFwd (relayOf l s) → RelayFwd (relayOf l s′)
legStep→rmono l s s′ (ldProd _ re _ _ _ _ _)     = subst RelayFwd re
legStep→rmono l s s′ (ldRelay rk _ _ _ _ _ _ _)  = rk-fwd-mono rk
legStep→rmono l s s′ (ldCons _ _ _ re _ _ _ _ _) = subst RelayFwd re
legStep→rmono l s s′ (ldFix _ re _ _ _ _ _)      = subst RelayFwd re

------------------------------------------------------------------------
-- The reflect bridge `reach-ev-driver`: land a visible api-CSBF middle at a
-- reachable `r′` (`toSys r′ = s′` definitionally) carrying leg-`l`'s genuine
-- `LegDriverStep`.  VERBATIM mirror of `PipeClassRelay.reach-ev-classrelay`,
-- with `PipeEvDriverCone.driverExpose` in place of `top-nodes-abs-expose-cls`.
------------------------------------------------------------------------

reach-ev-driver : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × LegDriverStep l (toSys r) (toSys r′) e a
      × (UpSrvEvo l (toSys r) (toSys r′) × DnSrvEvo l (toSys r) (toSys r′))
reach-ev-driver l r {X} {e} {a} aic apimem step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _   = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns refl with driverExpose (toSys r) apimem ns
...   | s′ , medEq , N₁≡ , cWeakRun , ldBD , ldCD , sBD , sCD =
        r′ , Mr , pickLeg l (toSys r) s′ ldBD ldCD , pickLegSrv l (toSys r) s′ sBD sCD
  where
    Meq′ : ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N₁) ∖ ioES) ≡ absDec s′
    Meq′ = cong₂ (λ mm nn → (decMed mm ∥⇘ ioES ⇙ nn) ∖ ioES) medEq N₁≡
    wrun : rdec r ═[ ev (evl (evLabel X e a)) ]═► ⟦ s′ ⟧
    wrun = subst (λ mm → rdec r ═[ ev (evl (evLabel X e a)) ]═►
                          ((decMed mm ∥⇘ ioES ⇙ nodesOf s′) ∖ ioES))
             medEq
             (lift-nodes-whole-wev (decMed (med (toSys r))) (nodesOf (toSys r))
               (SR.api∉ioES {X} {e} {a} aic)
               (noOffer→viewV _ (SR.medium-api-non-offer (med (toSys r)) aic))
               cWeakRun)
    r′ : RState
    r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
    Mr : ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N₁) ∖ ioES) ≡ radec r′
    Mr = trans Meq′ (sym (rcloseʷ-abs r {s′ = s′} wrun))

------------------------------------------------------------------------
-- BREAK.  A medium `break l₀` flips one link's `broken` flag, leaving the copy
-- cells (`phase`) and every node untouched — so all seven leg-`l` components are
-- fixed and the preservation is `pipeInv⁺-frame`.
--
-- `break-med-phase` re-mirrors `WalkBreakDrop.medium-break-drop` (the frozen
-- `SysRoute` break inversion), returning the concrete successor `m′ = mkMed
-- (phase m) (broken-upd …)` together with `phase m′ ≡ phase m` (`refl`) so the
-- cell fixities are available even though the medium object changed.
------------------------------------------------------------------------

-- a `break l₀` of `decMed m` lands at `m′` with `phase` PRESERVED
break-med-phase : (m : MedState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
  → decMed m ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M
  → Σ[ m′ ∈ MedState ] (M ≡ decMed m′) × (phase m′ ≡ phase m)
break-med-phase m l₀ step
    with ⦀Fin-ev-inv numLinks (λ i → decLink i (phase m i) (broken m i)) (SR.break-noBoth m) step
... | i , Mi , linkStep , Meq with SR.link-break-chan i (phase m i) (broken m i) linkStep
...   | _ , MiSkip =
        mkMed (phase m) (SR.broken-upd (broken m) i)
      , trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                     (finUpd (λ k → decLink k (phase m k) (broken m k)) i z)) MiSkip)
                 (SR.recon-decMed-brk m i))
      , refl

-- frame preservation across a pure-medium `broken`-flip: the nodes are shared
-- (so every driver / client fixity is `refl` once `l` is concrete) and `phase`
-- is preserved (`pheq`), so the two cell fixities follow by `cong`
frame-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
            → phase m′ ≡ phase (med s)
            → PipeInv⁺ l s → PipeInv⁺ l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
frame-break legBD s m′ pheq =
  pipeInv⁺-frame legBD s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) refl refl refl
    (cong (λ ph → ph linkAB hi N2N_BlockFetch) (sym pheq))
    (cong (λ ph → ph linkBD hi N2N_BlockFetch) (sym pheq)) refl refl
frame-break legCD s m′ pheq =
  pipeInv⁺-frame legCD s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) refl refl refl
    (cong (λ ph → ph linkAC hi N2N_BlockFetch) (sym pheq))
    (cong (λ ph → ph linkCD hi N2N_BlockFetch) (sym pheq)) refl refl

-- INVERSION ONLY (no `PipeInv⁺` anywhere in its statement): a visible
-- `break l₀` of `radec r` is a MEDIUM solo, landing at a concrete `m′` whose
-- `phase` is preserved.  This is the ONLY part of the break case that needs a
-- (nested, genuine) case split, and it is deliberately kept in its own
-- top-level function — see the assembly note on `evStep-break` below.
break-invert : (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
  → radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M
  → Σ[ m′ ∈ MedState ]
      (decMed (med (toSys r)) ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► decMed m′)
      × (phase m′ ≡ phase (med (toSys r)))
      × (M ≡ ((decMed m′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
break-invert r l₀ step
    with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
           (inj₂ (SR.absnodes-no-break (toSys r))) step
... | nodesEv N₁ ns _ = ⊥-elim (SR.absnodes-no-break (toSys r) (N₁ , ns))
... | medEv M₁ medStep refl with break-med-phase (med (toSys r)) l₀ medStep
...   | m′ , refl , pheq = m′ , medStep , pheq , refl

-- the visible-middle preservation for a `break l₀` event.
--
-- ASSEMBLY NOTE (blkA-parameterisation).  This clause must stay `with`-FREE.
-- Inside a `(blkA : Block₃)` module a `with`-abstraction partially NORMALISES
-- the goal, and the normal form of `PipeInv⁺ l (toSys r)` then refuses to
-- convert against the un-normalised `PipeInv⁺ l (toSys r)` of the body
-- (`prodOf l (RState.sys r) != prodOf l (toSys r)`, two printed-identical terms
-- separated only by the elided module-parameter slot).  All the case analysis
-- therefore lives in `break-invert`, whose statement mentions no `PipeInv⁺`, and
-- the assembly below is a single `let`, where `toSys r′` reduces to `s′` on the
-- nose and `frame-break`'s type matches the goal syntactically.
evStep-break : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
  → radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeInv⁺ l (toSys r) → PipeInv⁺ l (toSys r′))
evStep-break l r l₀ {a} step =
  let (m′ , medStep , pheq , Meq) = break-invert r l₀ {a} step
      s′ : SysState
      s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
      wrun : rdec r ═[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]═► ⟦ s′ ⟧
      wrun = wev τ*-refl
               (lift-med-whole-ev (decMed (med (toSys r))) (nodesOf (toSys r))
                 (SR.break∉ioES {l₀} {a}) medStep
                 (noOffer→viewV _ (SR.nodes-no-break (toSys r))))
               τ*-refl
      r′ : RState
      r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
  in  r′
    , trans Meq (sym (rcloseʷ-abs r {s′ = s′} wrun))
    , frame-break l (toSys r) m′ pheq

------------------------------------------------------------------------
-- The api-CSBF case: land the driver step at the reachable `r′` via the
-- reflect bridge and dispatch the (now self-contained) `LegDriverStep`.
-- `with`-FREE by design (blkA-parameterisation hazard): a single `let`, where
-- `toSys r′` reduces on the nose and `legStep→pres`'s type matches the goal
-- syntactically.
------------------------------------------------------------------------

evStep-api : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeInv⁺ l (toSys r) → PipeInv⁺ l (toSys r′))
evStep-api l r aic apimem step =
  let (r′ , Mr , ld , _) = reach-ev-driver l r aic apimem step
  in  r′ , Mr , legStep→pres l (toSys r) (toSys r′) ld

------------------------------------------------------------------------
-- `evStep` — the TOTAL visible-middle combinator (matches
-- `PipeStepEmit.EvStep l` exactly).  Label dispatch mirrors
-- `SysBisim.oevB-impl`: api-CSBF (apiCS/apiBF/done) → the driver bridge;
-- `break` → the medium frame case; io (input/output ∈ ioES) is HIDDEN
-- (`oevB-no-io`); the inert api events and the wire messages are refuted at
-- medium + abstract nodes (`oevB-refute`).
------------------------------------------------------------------------

evStep : (l : TwoLegs) → EvStep l
evStep l r {evLabel _ (apiCS l₀ d₀ m) a} step = evStep-api l r aicCS tt step
evStep l r {evLabel _ (apiBF l₀ d₀ m) a} step = evStep-api l r aicBF tt step
evStep l r {evLabel _ (done  l₀ d₀ id) a} step = evStep-api l r aicDone tt step
evStep l r {evLabel _ (break l₀) a} step = evStep-break l r l₀ step
evStep l r {evLabel _ (input  l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
evStep l r {evLabel _ (output l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
evStep l r {evLabel _ (apiKA l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiKA (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStep l r {evLabel _ (apiTS l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiTS (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStep l r {evLabel _ (apiLN l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLN (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStep l r {evLabel _ (apiLF l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLF (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStep l r {evLabel _ (sndmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndmsg (med (toSys r))) (SR.absnodes-no-sndmsg (toSys r)) step)
evStep l r {evLabel _ (rcvmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvmsg (med (toSys r))) (SR.absnodes-no-rcvmsg (toSys r)) step)
evStep l r {evLabel _ (tx     l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-tx (med (toSys r))) (SR.absnodes-no-tx (toSys r)) step)
evStep l r {evLabel _ (sndack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndack (med (toSys r))) (SR.absnodes-no-sndack (toSys r)) step)
evStep l r {evLabel _ (rcvack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvack (med (toSys r))) (SR.absnodes-no-rcvack (toSys r)) step)
evStep l r {evLabel _ (ack    l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-ack (med (toSys r))) (SR.absnodes-no-ack (toSys r)) step)

------------------------------------------------------------------------
-- SESSION-33 (G2) — the PRODUCT visible-step combinator `evStepS`.
--
-- `PipeInvProd.EvStepS l` is exactly the type below, but `PipeInvProd` IMPORTS
-- this module, so the type is spelled out here rather than imported (it is a
-- plain definition, so `evStepS` inhabits `PipeInvProd.EvStepS l` by
-- unfolding).  This is session-32's "cheaper packaging": the leaf builds
-- `EvStepS` DIRECTLY, with its own reflected `r′` and BOTH halves, so nothing
-- ever has to make `proj₁ (evStep l r st)` reduce.
--
-- The server half rides on `PipeSrvInv.srvCoupled-pres`, fed by
--   · the two consequent-monotone maps `legStep→pmono`/`legStep→rmono`, read
--     off the SAME `LegDriverStep` the `PipeInv⁺` half consumes, and
--   · the two server EVOLUTIONS `driverExpose` now returns (G2c).
------------------------------------------------------------------------

-- the product visible-step combinator type (≡ `PipeInvProd.EvStepS l`)
EvStepS′ : TwoLegs → Set₁
EvStepS′ l = (r : RState) {e : Event} {M : NetProc} → radec r ─[ ev (evl e) ]─► M
           → Σ[ r′ ∈ RState ]
               (M ≡ radec r′)
               × ((PipeInv⁺ l (toSys r) × SrvCoupled l (toSys r))
                  → (PipeInv⁺ l (toSys r′) × SrvCoupled l (toSys r′)))

-- the server-coupling frame across a pure-medium `broken`-flip.  MUST be cased
-- on `l` at the top: `prodOf`/`relayOf`/`upSrv`/`dnSrv` all pattern-match on the
-- leg, so with `l` a variable both sides stay stuck and Agda tries (and fails)
-- to unify `med (toSys r)` with the new `m′`.
srvCoupled-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
                 → SrvCoupled l s → SrvCoupled l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
srvCoupled-break legBD s m′ =
  srvCoupled-frame legBD s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) refl refl refl refl
srvCoupled-break legCD s m′ =
  srvCoupled-frame legCD s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) refl refl refl refl

-- the api-CSBF case at the product (mirror `evStep-api`; `with`-FREE)
evStepS-api : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × ((PipeInv⁺ l (toSys r) × SrvCoupled l (toSys r))
         → (PipeInv⁺ l (toSys r′) × SrvCoupled l (toSys r′)))
evStepS-api l r aic apimem step =
  let (r′ , Mr , ld , ue , de) = reach-ev-driver l r aic apimem step
  in  r′ , Mr
    , (λ ps → legStep→pres l (toSys r) (toSys r′) ld (proj₁ ps)
            , srvCoupled-pres l (toSys r) (toSys r′)
                (legStep→pmono l (toSys r) (toSys r′) ld)
                (legStep→rmono l (toSys r) (toSys r′) ld) ue de (proj₂ ps))

-- the `break` case at the product: a `broken`-flip moves NO node, so the
-- server coupling rides across by `srvCoupled-frame` (all four reads `refl`)
evStepS-break : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
  → radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × ((PipeInv⁺ l (toSys r) × SrvCoupled l (toSys r))
         → (PipeInv⁺ l (toSys r′) × SrvCoupled l (toSys r′)))
evStepS-break l r l₀ {a} step =
  let (m′ , medStep , pheq , Meq) = break-invert r l₀ {a} step
      s′ : SysState
      s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
      wrun : rdec r ═[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]═► ⟦ s′ ⟧
      wrun = wev τ*-refl
               (lift-med-whole-ev (decMed (med (toSys r))) (nodesOf (toSys r))
                 (SR.break∉ioES {l₀} {a}) medStep
                 (noOffer→viewV _ (SR.nodes-no-break (toSys r))))
               τ*-refl
      r′ : RState
      r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
  in  r′
    , trans Meq (sym (rcloseʷ-abs r {s′ = s′} wrun))
    , (λ ps → frame-break l (toSys r) m′ pheq (proj₁ ps)
            , srvCoupled-break l (toSys r) m′ (proj₂ ps))

-- `evStepS` — the TOTAL product visible-middle combinator (label dispatch
-- verbatim `evStep`'s)
evStepS : (l : TwoLegs) → EvStepS′ l
evStepS l r {evLabel _ (apiCS l₀ d₀ m) a} step = evStepS-api l r aicCS tt step
evStepS l r {evLabel _ (apiBF l₀ d₀ m) a} step = evStepS-api l r aicBF tt step
evStepS l r {evLabel _ (done  l₀ d₀ id) a} step = evStepS-api l r aicDone tt step
evStepS l r {evLabel _ (break l₀) a} step = evStepS-break l r l₀ step
evStepS l r {evLabel _ (input  l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
evStepS l r {evLabel _ (output l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
evStepS l r {evLabel _ (apiKA l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiKA (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepS l r {evLabel _ (apiTS l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiTS (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepS l r {evLabel _ (apiLN l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLN (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepS l r {evLabel _ (apiLF l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLF (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepS l r {evLabel _ (sndmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndmsg (med (toSys r))) (SR.absnodes-no-sndmsg (toSys r)) step)
evStepS l r {evLabel _ (rcvmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvmsg (med (toSys r))) (SR.absnodes-no-rcvmsg (toSys r)) step)
evStepS l r {evLabel _ (tx     l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-tx (med (toSys r))) (SR.absnodes-no-tx (toSys r)) step)
evStepS l r {evLabel _ (sndack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndack (med (toSys r))) (SR.absnodes-no-sndack (toSys r)) step)
evStepS l r {evLabel _ (rcvack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvack (med (toSys r))) (SR.absnodes-no-rcvack (toSys r)) step)
evStepS l r {evLabel _ (ack    l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-ack (med (toSys r))) (SR.absnodes-no-ack (toSys r)) step)

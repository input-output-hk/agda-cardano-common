{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — `deliver`: the TOTAL per-observable-step reflector
-- feeding `WalkEngine.walkPosFrom`'s `deliver` parameter
-- (`Praos.WalkDeliver`).
--
-- Under a reachable, PENDING (`Pr b r`) state, `deliver` dispatches the head
-- of a `WTrace` of `abstractSystem`:
--
--   · `step` on a visible api event (`apiCS`/`apiBF`/`done` — `IsApiCSBF`):
--     lift it with `WalkReachExpose.liftReach-ev-expose` (reachable successor
--     `r′` + strict `μTot` drop + `WalkDExpose.DReport`), then classify the
--     `DReport` with `WalkPr.Pr-step` (which TRACKS the pending leg).  A
--     NON-delivering step yields `inj₂ (r′ , … , Pr b r′)` (same leg); a
--     `recvBFBlock@{BD,CD}` DELIVERING step (`Pr-step`'s leg-tagged
--     `DeliverSig`, whose pinned label is `apiBF (linkOf leg) hi recvBFBlock`)
--     yields `inj₁ arrivedD`.  In every non-`recvBFBlock` label branch the
--     `DeliverSig` alternative is dynamically impossible and is discharged by
--     the label-id contradiction (`isRecvBF`).
--   · `step` on a `break l`: `WalkReachExpose.liftReach-break-expose` (always a
--     `dFix` report — a break is a medium solo) ⇒ `Pr` preserved ⇒ `inj₂`.
--   · `step` on an inert api (`apiKA/TS/LN/LF`) or a hidden/wire io event: the
--     weak step is refuted by lifting its τ*-prefix to a reachable descendant
--     (`WalkTauExpose.liftτ*-expose`) and applying the frozen R2 refutations
--     `SysBisim.oevB-no-io` / `SysBisim.oevB-refute` at that descendant.
--   · `step` on a `√`, `done`, `stuck`: the FRONTIER-A terminal refutations
--     `WalkEnabled.wenabled-{sqrt,done,stuck}-⊥` (threading `wprog`).
--   · `div`: `WalkConvNoDiv.absNoDiv`.
--
-- BLOCK-IDENTITY.  `arrivedD b`'s frozen `a ≡ b` conjunct is unprovable inside
-- `deliver`: `Pr` is block-blind and `b` is universally quantified, so neither
-- `b″ ≡ blkA` (a copy-cell value invariant, unbuilt) nor `b ≡ blkA` (which lives
-- only in `locate`) is available here.  Per the sanctioned R3 fallback the
-- `a ≡ b` conjunct has been DROPPED from `arrivedD` (see
-- `FourNodeDiamondLiveness`), so `arrivedD` now fires on any D-`recvBFBlock@hi`.
--
-- No postulate/hole/meta.  `wprog` is a module PREMISE.  Models + R2-frozen
-- modules stay READ-ONLY (imported only).
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
import Data.Unit as U
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Nat using ( _<_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDeliver (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Base using ( hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Link
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack
        ; recvBFBlock; sendBFBlock; sendBFBatchDone; reqBFRange
        ; sendBFRequestRange; sendBFClientDone; sendBFStartBatch; sendBFNoBlocks )
  renaming ( done to netDone )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; Event√; evl; √; evLabel; ev; _─[_]─►_ )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; _─[τ*]─►_ )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( atom )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; step; done; stuck; div; ⟦_⟧ᵂ; tailIdx )
open import Semantics.LTL.Fairness
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WEnabled )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( μTot )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkEngine blkA
  using ( Confᵂ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( Pr; Pr-step; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkReachExpose blkA
  using ( liftReach-ev-expose; liftReach-break-expose )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkTauExpose blkA
  using ( liftτ*-expose )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvNoDiv blkA
  using ( absNoDiv )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkEnabled blkA as WEn
open WEn using ( IntactApiClass )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA as SB
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA as SO
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( arrivedD⁻ )

------------------------------------------------------------------------
-- `isRecvBF e` — the event `e` is exactly a `recvBFBlock` api event.  Used to
-- discharge `Pr-step`'s c34 (delivering) alternatives in the label branches
-- where they are dynamically impossible: the pinned c34 label is `apiBF … hi
-- recvBFBlock`, so `subst isRecvBF (sym lbl) U.tt` transports `⊤` onto a
-- non-`recvBFBlock` event, whose `isRecvBF` reduces to `⊥`.
------------------------------------------------------------------------

isRecvBF : Event → Set
isRecvBF (evLabel _ (apiBF _ _ recvBFBlock) _) = U.⊤
isRecvBF _ = ⊥

------------------------------------------------------------------------
-- WEAK refutation of a visible event that no reachable state offers: lift the
-- weak step's τ*-prefix to a reachable descendant `r₁` (`liftτ*-expose`), then
-- apply the given per-state STRONG refutation there.
------------------------------------------------------------------------

refute-weak : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
            → ((r₁ : RState) {M : NetProc} → radec r₁ ─[ ev (evl (evLabel X e a)) ]─► M → ⊥)
            → radec r ═[ ev (evl (evLabel X e a)) ]═► t′ → ⊥
refute-weak r {X} {e} {a} ref (wev pre mid post) with liftτ*-expose r pre
... | r₁ , eq₁ , _ , _ =
      ref r₁ (subst (λ z → z ─[ ev (evl (evLabel X e a)) ]─► _) eq₁ mid)

------------------------------------------------------------------------
-- `deliver` — TOTAL over the WTrace head, at a fixed block `b` and the
-- FRONTIER-A weak-progress premise `wprog`.
------------------------------------------------------------------------

module _
  (b : Block₃)
  (wprog : (r : RState) → Pr b r → WEnabled (IntactApiClass b) (radec r))
  where

  deliver : (r : RState) → Pr b r
          → (w : WTrace (⊤ {0ℓ}) (radec r)) → Confᵂ w
          → ⟦ atom arrivedD⁻ ⟧ᵂ w
          ⊎ Σ[ r′ ∈ RState ] (tailIdx w ≡ radec r′)
              × (μTot (toSys r′) < μTot (toSys r)) × Pr b r′

  -- terminal frames: refuted by the FRONTIER-A refutations / `absNoDiv`
  deliver r pr (done run eq)  _ = ⊥-elim (WEn.wenabled-done-⊥  b wprog r pr run eq)
  deliver r pr (stuck run st) _ = ⊥-elim (WEn.wenabled-stuck-⊥ b wprog r pr run st)
  deliver r pr (div dv)       _ = ⊥-elim (absNoDiv r dv)

  -- √-step: the terminal √ refutation
  deliver r pr (step {e = √ x} wstep _) _ =
    ⊥-elim (WEn.wenabled-sqrt-⊥ b wprog r pr wstep)

  -- apiCS (driver-advance, never delivering): successor, c34 impossible
  deliver r pr (step {e = evl (evLabel _ (apiCS l₀ d₀ m) a)} wstep _) _
    with liftReach-ev-expose r SO.aicCS tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)

  -- apiBF recvBFBlock: the DELIVERING hop — c34 on BD/CD builds `arrivedD`
  deliver r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ recvBFBlock) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (legBD , _ , _ , _ , refl , _) = inj₁ (inj₁ refl , refl)
  ...   | inj₂ (legCD , _ , _ , _ , refl , _) = inj₁ (inj₂ refl , refl)

  -- apiBF non-delivering tags: successor, c34 impossible
  deliver r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFBlock) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliver r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFBatchDone) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliver r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ reqBFRange) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliver r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFRequestRange) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliver r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFClientDone) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliver r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFStartBatch) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)
  deliver r pr (step {e = evl (evLabel _ (apiBF l₀ d₀ sendBFNoBlocks) a)} wstep _) _
    with liftReach-ev-expose r SO.aicBF tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)

  -- done (api, driver receives CS-server callback): successor, c34 impossible
  deliver r pr (step {e = evl (evLabel _ (netDone l₀ d₀ id) a)} wstep _) _
    with liftReach-ev-expose r SO.aicDone tt wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)

  -- break: medium solo (`dFix`) ⇒ `Pr` preserved ⇒ successor
  deliver r pr (step {e = evl (evLabel _ (break l₀) a)} wstep _) _
    with liftReach-break-expose r l₀ wstep
  ... | r′ , eq , lt , drep with Pr-step b {r} {r′} pr drep
  ...   | inj₁ pr′                        = inj₂ (r′ , eq , lt , pr′)
  ...   | inj₂ (_ , _ , _ , _ , lbl , _)  = ⊥-elim (subst isRecvBF (sym lbl) U.tt)

  -- inert api events (not `IsApiCSBF`): no reachable state offers them
  deliver r pr (step {e = evl (evLabel _ (apiKA l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiKA (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st) wstep)
  deliver r pr (step {e = evl (evLabel _ (apiTS l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiTS (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st) wstep)
  deliver r pr (step {e = evl (evLabel _ (apiLN l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiLN (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st) wstep)
  deliver r pr (step {e = evl (evLabel _ (apiLF l₀ d₀ m) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiLF (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st) wstep)

  -- hidden io events: `∖ ioES` makes them invisible (`oevB-no-io`)
  deliver r pr (step {e = evl (evLabel _ (input l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r (λ r₁ st → SB.oevB-no-io r₁ tt st) wstep)
  deliver r pr (step {e = evl (evLabel _ (output l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r (λ r₁ st → SB.oevB-no-io r₁ tt st) wstep)

  -- wire events: offered by neither the medium nor the abstract nodes
  deliver r pr (step {e = evl (evLabel _ (sndmsg l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-sndmsg (med (toSys r₁)))
                    (SR.absnodes-no-sndmsg (toSys r₁)) st) wstep)
  deliver r pr (step {e = evl (evLabel _ (rcvmsg l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-rcvmsg (med (toSys r₁)))
                    (SR.absnodes-no-rcvmsg (toSys r₁)) st) wstep)
  deliver r pr (step {e = evl (evLabel _ (tx l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-tx (med (toSys r₁)))
                    (SR.absnodes-no-tx (toSys r₁)) st) wstep)
  deliver r pr (step {e = evl (evLabel _ (sndack l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-sndack (med (toSys r₁)))
                    (SR.absnodes-no-sndack (toSys r₁)) st) wstep)
  deliver r pr (step {e = evl (evLabel _ (rcvack l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-rcvack (med (toSys r₁)))
                    (SR.absnodes-no-rcvack (toSys r₁)) st) wstep)
  deliver r pr (step {e = evl (evLabel _ (ack l₀ d₀ id) a)} wstep _) _ =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-ack (med (toSys r₁)))
                    (SR.absnodes-no-ack (toSys r₁)) st) wstep)

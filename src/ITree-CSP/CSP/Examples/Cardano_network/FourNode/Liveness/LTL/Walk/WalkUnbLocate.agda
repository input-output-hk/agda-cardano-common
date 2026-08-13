{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 (SESSION-34, `wprog` discharge) — the CONFINED-GROUP
-- unbrokenness fold and the augmented locate (`Praos.WalkUnbLocate`).
--
-- The walk needs `Unb gs` (both protected links unbroken) AT the located
-- `producedA` frame.  `PipeLocate.locate`'s reachable `r0` is opaque, so
-- `Unb` cannot be read off it directly; instead:
--
--   · `unbAlong` — an INDEPENDENT fold from `rinit` along the same trace
--     (mirror of `PipeInvProd.pipeInvS-along-walk′`'s backbone), carrying
--     `Unb gs` via the `WalkBrkLift` flag lifts: api/done and hidden-τ
--     steps FIX every flag, a `break l₀` step is confined by the trace
--     hypothesis (`head-not-prot`: `l₀` is not a protected link) so
--     `bupd-miss` preserves both protected flags; every other event class
--     is refuted exactly as in `WalkDeliver`.
--   · `locateU` — `PipeLocate.locate` (for `Pr`) + `unbAlong` (for `Unb`),
--     glued by the DECODE TRANSPORT `WalkBrkFire.unbT` at the shared frame
--     index (`radec r0 ≡ radec rᵤ`) — the two folds' states need never be
--     syntactically related.
--
-- No postulate/hole/meta; no `dne`.  All base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ; Lift; lift; lower )
open import Data.Unit.Polymorphic using ( ⊤; tt )
import Data.Unit as U
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Nat using ( ℕ; zero; suc )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Function using ( case_of_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; _≢_; refl; sym; trans; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkUnbLocate (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Base using ( hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Link
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack )
  renaming ( done to netDone )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Event; Event√; evl; √; evLabel; ev; _─[_]─►_ )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; _─[τ*]─►_ )
open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( LTLᵗ; atom; ¬_ )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; ∞WTrace; step; done; stuck; div; ⟦_⟧ᵂ; frameOf; IsTermᵂ
        ; drop; dropIdx; tail; tailIdx; dropIdx-stutter )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA; brkG1; brkG2 )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( NetProc; RState; radec; toSys; rinit; radec-init )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( G⁺ᵂ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( Pr )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkCausal blkA
  using ( term-no-prod; noWeakVis-deadlock; sqrt-target-deadlock )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDeliver blkA
  using ( refute-weak )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA as SB
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA as SO
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeLocate blkA as PL
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBrkFire blkA
  using ( GSide; g1; g2; protA; protB; Unb; unbFix; unbT )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkBrkLift blkA
  using ( liftReach-ev-brk; liftReach-break-brk )

------------------------------------------------------------------------
-- The side-fixed trace confinement and the head-event extraction.
------------------------------------------------------------------------

-- the break atom a side's confinement forbids
brkOf : GSide → _
brkOf g1 = brkG1
brkOf g2 = brkG2

-- the side-fixed confinement of a (suffix) trace: `G⁺(¬ brkOf gs)`
Cfᵂ : (gs : GSide) {t : NetProc} → WTrace (⊤ {0ℓ}) t → Set
Cfᵂ gs w = G⁺ᵂ (¬ atom (brkOf gs)) w

-- a confined trace's HEAD `break l₀` is not on a protected link (read the
-- `m = 0` instance of the `G⁺`; `brkOf gs` at the head frame is the ⊎)
head-not-prot : (gs : GSide) {t t′ : NetProc} {l₀ : Link} {a : ⊤₀}
    (wstep : t ═[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]═► t′)
    (tr : ∞WTrace (⊤ {0ℓ}) t′)
  → Cfᵂ gs (step wstep tr)
  → (l₀ ≢ protA gs) × (l₀ ≢ protB gs)
head-not-prot g1 wstep tr cf =
  (λ q → ⊥-elim (lower (cf 0 (inj₁ q)))) , (λ q → ⊥-elim (lower (cf 0 (inj₂ q))))
head-not-prot g2 wstep tr cf =
  (λ q → ⊥-elim (lower (cf 0 (inj₁ q)))) , (λ q → ⊥-elim (lower (cf 0 (inj₂ q))))

-- confinement restricts to the tail (definitional `drop (suc m) w`)
Cf-tail : (gs : GSide) {t : NetProc} (w : WTrace (⊤ {0ℓ}) t)
  → Cfᵂ gs w → Cfᵂ gs (tail w)
Cf-tail gs w cf m = cf (suc m)

------------------------------------------------------------------------
-- The Unb fold along the trace (mirror `PipeInvProd.pipeInvS-along-walk′`'s
-- backbone; the step dispatch mirrors `WalkDeliver.deliver`'s label classes,
-- with ONE uniform `apiBF` clause — `Unb` does not care which tag fired).
------------------------------------------------------------------------

module _ (gs : GSide) (b : Block₃) where

  -- fold `Unb gs` from `r` to the `producedA` frame at position `n`
  unbAlong′ : (r : RState) {t : NetProc} → t ≡ radec r → Unb gs (toSys r)
            → (w : WTrace (⊤ {0ℓ}) t) → Cfᵂ gs w → (n : ℕ)
            → producedA b (frameOf (drop n w))
            → Σ[ r′ ∈ RState ] (dropIdx n w ≡ radec r′) × Unb gs (toSys r′)
  unbAlong′ r eq unb w cf zero pn = r , eq , unb

  -- apiCS: nodes-solo, flags fixed
  unbAlong′ r eq unb (step {e = evl (evLabel _ (apiCS l₀ d₀ m₀) a)} wstep tr) cf (suc m) pn
    with liftReach-ev-brk r SO.aicCS tt
           (subst (λ z → z ═[ ev (evl (evLabel _ (apiCS l₀ d₀ m₀) a)) ]═► _) eq wstep)
  ... | r₁ , eq₁ , bfix =
        unbAlong′ r₁ eq₁ (unbFix (toSys r) (toSys r₁) gs bfix unb)
          (tail (step {e = evl (evLabel _ (apiCS l₀ d₀ m₀) a)} wstep tr))
          (Cf-tail gs (step {e = evl (evLabel _ (apiCS l₀ d₀ m₀) a)} wstep tr) cf) m pn

  -- apiBF (ANY tag): nodes-solo, flags fixed
  unbAlong′ r eq unb (step {e = evl (evLabel _ (apiBF l₀ d₀ m₀) a)} wstep tr) cf (suc m) pn
    with liftReach-ev-brk r SO.aicBF tt
           (subst (λ z → z ═[ ev (evl (evLabel _ (apiBF l₀ d₀ m₀) a)) ]═► _) eq wstep)
  ... | r₁ , eq₁ , bfix =
        unbAlong′ r₁ eq₁ (unbFix (toSys r) (toSys r₁) gs bfix unb)
          (tail (step {e = evl (evLabel _ (apiBF l₀ d₀ m₀) a)} wstep tr))
          (Cf-tail gs (step {e = evl (evLabel _ (apiBF l₀ d₀ m₀) a)} wstep tr) cf) m pn

  -- done (CS-server callback): nodes-solo, flags fixed
  unbAlong′ r eq unb (step {e = evl (evLabel _ (netDone l₀ d₀ id) a)} wstep tr) cf (suc m) pn
    with liftReach-ev-brk r SO.aicDone tt
           (subst (λ z → z ═[ ev (evl (evLabel _ (netDone l₀ d₀ id) a)) ]═► _) eq wstep)
  ... | r₁ , eq₁ , bfix =
        unbAlong′ r₁ eq₁ (unbFix (toSys r) (toSys r₁) gs bfix unb)
          (tail (step {e = evl (evLabel _ (netDone l₀ d₀ id) a)} wstep tr))
          (Cf-tail gs (step {e = evl (evLabel _ (netDone l₀ d₀ id) a)} wstep tr) cf) m pn

  -- break l₀: confined ⇒ l₀ is NOT protected ⇒ both protected flags fixed
  unbAlong′ r eq unb (step {e = evl (evLabel _ (break l₀) a)} wstep tr) cf (suc m) pn
    with liftReach-break-brk r l₀
           (subst (λ z → z ═[ ev (evl (evLabel _ (break l₀) a)) ]═► _) eq wstep)
       | head-not-prot gs (subst (λ z → z ═[ ev (evl (evLabel _ (break l₀) a)) ]═► _) refl wstep) tr cf
  ... | r₁ , eq₁ , bupd | notA , notB =
        unbAlong′ r₁ eq₁
          ( trans (bupd (protA gs) (λ q → notA (sym q))) (proj₁ unb)
          , trans (bupd (protB gs) (λ q → notB (sym q))) (proj₂ unb) )
          (tail (step {e = evl (evLabel _ (break l₀) a)} wstep tr))
          (Cf-tail gs (step {e = evl (evLabel _ (break l₀) a)} wstep tr) cf) m pn

  -- inert api events (apiKA/TS/LN/LF): no reachable state offers them
  unbAlong′ r eq unb (step {e = evl (evLabel _ (apiKA l₀ d₀ m₀) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiKA (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (apiKA l₀ d₀ m₀) a)) ]═► _) eq wstep))
  unbAlong′ r eq unb (step {e = evl (evLabel _ (apiTS l₀ d₀ m₀) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiTS (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (apiTS l₀ d₀ m₀) a)) ]═► _) eq wstep))
  unbAlong′ r eq unb (step {e = evl (evLabel _ (apiLN l₀ d₀ m₀) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiLN (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (apiLN l₀ d₀ m₀) a)) ]═► _) eq wstep))
  unbAlong′ r eq unb (step {e = evl (evLabel _ (apiLF l₀ d₀ m₀) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-apiLF (med (toSys r₁)))
                    (SR.absnodes-no-nonCSBF (toSys r₁) tt (λ ())) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (apiLF l₀ d₀ m₀) a)) ]═► _) eq wstep))

  -- hidden io events: `∖ ioES` makes them invisible
  unbAlong′ r eq unb (step {e = evl (evLabel _ (input l₀ d₀ id) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r (λ r₁ st → SB.oevB-no-io r₁ tt st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (input l₀ d₀ id) a)) ]═► _) eq wstep))
  unbAlong′ r eq unb (step {e = evl (evLabel _ (output l₀ d₀ id) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r (λ r₁ st → SB.oevB-no-io r₁ tt st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (output l₀ d₀ id) a)) ]═► _) eq wstep))

  -- wire events: offered by neither the medium nor the abstract nodes
  unbAlong′ r eq unb (step {e = evl (evLabel _ (sndmsg l₀ d₀ id) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-sndmsg (med (toSys r₁)))
                    (SR.absnodes-no-sndmsg (toSys r₁)) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (sndmsg l₀ d₀ id) a)) ]═► _) eq wstep))
  unbAlong′ r eq unb (step {e = evl (evLabel _ (rcvmsg l₀ d₀ id) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-rcvmsg (med (toSys r₁)))
                    (SR.absnodes-no-rcvmsg (toSys r₁)) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (rcvmsg l₀ d₀ id) a)) ]═► _) eq wstep))
  unbAlong′ r eq unb (step {e = evl (evLabel _ (tx l₀ d₀ id) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-tx (med (toSys r₁)))
                    (SR.absnodes-no-tx (toSys r₁)) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (tx l₀ d₀ id) a)) ]═► _) eq wstep))
  unbAlong′ r eq unb (step {e = evl (evLabel _ (sndack l₀ d₀ id) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-sndack (med (toSys r₁)))
                    (SR.absnodes-no-sndack (toSys r₁)) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (sndack l₀ d₀ id) a)) ]═► _) eq wstep))
  unbAlong′ r eq unb (step {e = evl (evLabel _ (rcvack l₀ d₀ id) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-rcvack (med (toSys r₁)))
                    (SR.absnodes-no-rcvack (toSys r₁)) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (rcvack l₀ d₀ id) a)) ]═► _) eq wstep))
  unbAlong′ r eq unb (step {e = evl (evLabel _ (ack l₀ d₀ id) a)} wstep tr) cf (suc m) pn =
    ⊥-elim (refute-weak r
      (λ r₁ st → SB.oevB-refute r₁ (SR.medium-no-ack (med (toSys r₁)))
                    (SR.absnodes-no-ack (toSys r₁)) st)
      (subst (λ z → z ═[ ev (evl (evLabel _ (ack l₀ d₀ id) a)) ]═► _) eq wstep))

  -- a `√`-step: the tail lives over `deadlock`, hence terminal ⇒ no `producedA`
  unbAlong′ r eq unb (step {e = √ x} wstep tr) cf (suc m) pn =
    ⊥-elim (term-no-prod b (tail (step {e = √ x} wstep tr)) termTail m pn)
    where
      tdead : tailIdx (step {e = √ x} wstep tr) ≡ _
      tdead = sqrt-target-deadlock wstep
      termTail : IsTermᵂ (tail (step {e = √ x} wstep tr))
      termTail with tail (step {e = √ x} wstep tr)
      ... | step wstep₂ _ =
              ⊥-elim (noWeakVis-deadlock (subst (λ z → z ═[ ev _ ]═► _) tdead wstep₂))
      ... | done _ _  = U.tt
      ... | stuck _ _ = U.tt
      ... | div _     = U.tt

  -- terminal frames: `dropIdx` stutters back to the start index; `Unb` kept
  unbAlong′ r eq unb (done q eqr) cf (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (done q eqr) U.tt) eq , unb
  unbAlong′ r eq unb (stuck q st) cf (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (stuck q st) U.tt) eq , unb
  unbAlong′ r eq unb (div dv) cf (suc m) pn =
    r , trans (dropIdx-stutter (suc m) (div dv) U.tt) eq , unb

  -- seeded at `rinit` (every link unbroken: both components reduce to `refl`)
  unbAlong : (tr : WTrace (⊤ {0ℓ}) abstractSystem) → Cfᵂ gs tr → (n : ℕ)
           → producedA b (frameOf (drop n tr))
           → Σ[ r′ ∈ RState ] (dropIdx n tr ≡ radec r′) × Unb gs (toSys r′)
  unbAlong tr cf n pn = unbAlong′ rinit (sym radec-init) (refl , refl) tr cf n pn

  ------------------------------------------------------------------------
  -- `locateU` — `PipeLocate.locate` (Pr) + `unbAlong` (Unb), glued by the
  -- decode transport at the shared frame index.
  ------------------------------------------------------------------------

  -- the Unb-augmented locate: the walk's start carries BOTH `Pr` and `Unb`
  locateU : (tr : WTrace (⊤ {0ℓ}) abstractSystem) → Cfᵂ gs tr → (n : ℕ)
          → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
          → Σ[ r0 ∈ RState ] (dropIdx n tr ≡ radec r0) × Pr b r0 × Unb gs (toSys r0)
  locateU tr cf n pn =
    let (r0 , eq0 , pr)  = PL.locate b tr n pn
        (rᵤ , equ , unb) = unbAlong tr cf n pn
    in  r0 , eq0 , pr , unbT (toSys rᵤ) (toSys r0) gs (trans (sym equ) eq0) unb

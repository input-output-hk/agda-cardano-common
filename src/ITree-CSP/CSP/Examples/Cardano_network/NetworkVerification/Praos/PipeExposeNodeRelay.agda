{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the NODE RELAY exposure cone + τ-run
-- (`Praos.PipeExposeNodeRelay`).
--
-- The producer counterpart `PipeExposeNodeProd` exposes, across a hidden τ-run,
-- how the leg's node-A producer driver advances (`AllProdAdv`).  This module is
-- the RELAY counterpart: how the leg's relay driver phase (`relayOf`, a `CPPh` —
-- node B's `cp-B` for leg BD, node C's `cp-C` for leg CD) advances across the
-- same τ-paddings — in particular reaching a FORWARDED phase (`RelayFwd`,
-- `producing _ pp6…pp9`, the downstream delivery gate the `PipeInv⁺` coupling
-- reads).
--
-- RECIPE (identical to the client/producer, session-8/9 adaptation).  A
-- permissive reflexive-transitive advance `RelayAdv` with a TOTAL one-step
-- classifier `adv-of : (q q′) → RelayAdv q q′` (flagging `rFwd` exactly when the
-- target satisfies the genuine `RelayFwd` property — sound and when-agnostic).
-- Since `WalkConvNodeFix.top-nodes-io-abs-fix` already reflects the io-sync to a
-- successor carrying the relay's concrete new phase, `RelayAdv` reads DIRECTLY
-- off `s′` — `top-nodes-io-abs-relay` is a thin wrapper, no per-peer threading.
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeNodeRelay (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev; wτ )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( NetProc; absNodesOf; nodesOf; lift-med-whole-τ
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( CPPh; consuming; producing
        ; ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9 )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvEvInv blkA
  using ( medium-ev-inv-wt )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvNodeFix blkA
  using ( top-nodes-io-abs-fix )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysBisim blkA
  using ( lift-io-sync-whole-wτ )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA
  using ( setCell; absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( relayOf; RelayFwd )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA
  using ( IsApiCSBF )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.Walk blkA
  using ( μTot )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeReach blkA
  using ( reach-ev-both )

------------------------------------------------------------------------
-- The relay phase-advance algebra.  `Relay1` is one legal single move of a
-- relay driver: either it reached a FORWARDED phase (`rFwd`, carrying the genuine
-- `RelayFwd` property — the downstream `sendBFBlock` gate), or it made some other
-- move (`rAdv`).  `RelayAdv` is its reflexive-transitive closure (mirror
-- `PipeExposeNodeProd.ProdAdv`).
------------------------------------------------------------------------

-- one legal relay move (target-classified: forwarded-gate vs other move)
data Relay1 : CPPh → CPPh → Set where
  rFwd : ∀ {q q′} → RelayFwd q′ → Relay1 q q′   -- reached a forwarded phase
  rAdv : ∀ {q q′} → Relay1 q q′                  -- some other move

-- the reflexive-transitive closure: a relay's phase across a whole run
data RelayAdv : CPPh → CPPh → Set where
  rl-refl : ∀ {q}     → RelayAdv q q
  rl-step : ∀ {q r s} → Relay1 q r → RelayAdv r s → RelayAdv q s

-- `RelayAdv` composes (transitive), so it threads across a τ-run
rl-trans : ∀ {q r s} → RelayAdv q r → RelayAdv r s → RelayAdv q s
rl-trans rl-refl          g = g
rl-trans (rl-step x rest) g = rl-step x (rl-trans rest g)

------------------------------------------------------------------------
-- The pure classify: any concrete successor phase yields a one-step `RelayAdv`
-- (a forwarded phase `producing _ pp6…pp9` is flagged `rFwd`; every other phase
-- is `rAdv`).  Total on the successor — no weight bookkeeping needed.
------------------------------------------------------------------------

-- one relay move as a `RelayAdv`, classified by the concrete successor phase
adv-of : (q q′ : CPPh) → RelayAdv q q′
adv-of q (consuming b cp)  = rl-step rAdv rl-refl
adv-of q (producing b pp0) = rl-step rAdv rl-refl
adv-of q (producing b pp1) = rl-step rAdv rl-refl
adv-of q (producing b pp2) = rl-step rAdv rl-refl
adv-of q (producing b pp3) = rl-step rAdv rl-refl
adv-of q (producing b pp4) = rl-step rAdv rl-refl
adv-of q (producing b pp5) = rl-step rAdv rl-refl
adv-of q (producing b pp6) = rl-step (rFwd tt) rl-refl
adv-of q (producing b pp7) = rl-step (rFwd tt) rl-refl
adv-of q (producing b pp8) = rl-step (rFwd tt) rl-refl
adv-of q (producing b pp9) = rl-step (rFwd tt) rl-refl

------------------------------------------------------------------------
-- The whole-nodes relay report `AllRelayAdv`: a `RelayAdv` for EACH of the two
-- `PipeInv`-tracked relay drivers (the two legs' relays — `cp-B` on node B,
-- `cp-C` on node C).
------------------------------------------------------------------------

-- the two tracked relay drivers advance together
AllRelayAdv : SysState → SysState → Set
AllRelayAdv s s′ =
    RelayAdv (relayOf legBD s) (relayOf legBD s′)
  × RelayAdv (relayOf legCD s) (relayOf legCD s′)

-- reflexivity: a nodes-fixed step keeps every tracked relay (the frame case)
allRelayAdv-refl : (s : SysState) → AllRelayAdv s s
allRelayAdv-refl s = rl-refl , rl-refl

-- transitivity (pointwise): compose two relay reports across a τ-run
allRelayAdv-trans : (s s₁ s₂ : SysState)
                  → AllRelayAdv s s₁ → AllRelayAdv s₁ s₂ → AllRelayAdv s s₂
allRelayAdv-trans s s₁ s₂ (u₁ , v₁) (u₂ , v₂) =
    rl-trans u₁ u₂ , rl-trans v₁ v₂

-- TOTAL classify: any successor state yields an `AllRelayAdv` (`adv-of`).
allRelayAdv-of : (s s′ : SysState) → AllRelayAdv s s′
allRelayAdv-of s s′ =
    adv-of (relayOf legBD s) (relayOf legBD s′)
  , adv-of (relayOf legCD s) (relayOf legCD s′)

------------------------------------------------------------------------
-- TOP: the whole-nodes io-sync RELAY exposure (`top-nodes-io-abs-relay`).  A
-- thin wrapper over the frozen `top-nodes-io-abs-fix` (mirror
-- `PipeExposeNodeProd.top-nodes-io-abs-prod`), attaching the `AllRelayAdv` read
-- off the reflected `s′` via the total `allRelayAdv-of`.
------------------------------------------------------------------------

top-nodes-io-abs-relay : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllRelayAdv s s′
top-nodes-io-abs-relay s iomem step with top-nodes-io-abs-fix s iomem step
... | s′ , meq , Meq , wrun , _ , _ , _ , _ , _ , _ =
      s′ , meq , Meq , wrun , allRelayAdv-of s s′

------------------------------------------------------------------------
-- MEDIUM-τ reflector with the relay report (LIGHT — mirror
-- `PipeExposeNodeProd.τreflect-med-prod`): a medium drain moves NO node, so
-- every tracked relay is fixed (`allRelayAdv-refl`).
------------------------------------------------------------------------

τreflect-med-relay : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllRelayAdv (toSys r) (toSys r′)
τreflect-med-relay r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , _ , _ , M′≡ = r′ , Meq′ , allRelayAdv-refl (toSys r)
  where
    m′ : MedState
    m′ = mkMed (phase-upd (phase (med (toSys r))) i (flipCell (phase (med (toSys r)) i) d₀ id₀))
               (broken (med (toSys r)))
    s′ : SysState
    s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = wτ (τ*-step
             (lift-med-whole-τ (decMed (med (toSys r))) (nodesOf (toSys r))
               (subst (λ z → decMed (med (toSys r)) ─[ τ ]─► z) M′≡ ms))
             τ*-refl)
    r′ : RState
    r′ = mkR s′ (rStepʷ (reach r) wrun)
    Meq′ : M ≡ radec r′
    Meq′ = trans Meq (cong (λ z → (z ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES) M′≡)

------------------------------------------------------------------------
-- io-SYNC reflector with the relay report (RAM-heavy — mirror
-- `PipeExposeNodeProd.τreflect-io-prod`, using `top-nodes-io-abs-relay`).
------------------------------------------------------------------------

τreflect-io-relay : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllRelayAdv (toSys r) (toSys r′)
τreflect-io-relay r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt (med (toSys r)) iomem sM
       | top-nodes-io-abs-relay (toSys r) iomem sN
... | i , d₀ , id₀ , np , _ , M₁≡ | s″ , _ , N₁≡ , cWeakRun , relayRep =
      r′ , Meq′ , relayRep
  where
    m′ : MedState
    m′ = mkMed (phase-upd (phase (med (toSys r))) i (setCell (phase (med (toSys r)) i) d₀ id₀ np))
               (broken (med (toSys r)))
    s′ : SysState
    s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
    medWeak : decMed (med (toSys r)) ═[ ev (evl (evLabel X e a)) ]═► decMed m′
    medWeak = wev τ*-refl
                (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM)
                τ*-refl
    wrun : rdec r ═[ τ ]═► ⟦ s′ ⟧
    wrun = lift-io-sync-whole-wτ (decMed (med (toSys r))) (nodesOf (toSys r)) iomem medWeak cWeakRun
    r′ : RState
    r′ = mkR s′ (rStepʷ (reach r) wrun)
    Meq′ : M ≡ radec r′
    Meq′ = trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡)

------------------------------------------------------------------------
-- TOTAL per-τ reflector with the relay report (mirror
-- `PipeExposeNodeProd.τreflect-prod`).
------------------------------------------------------------------------

τreflect-relay : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllRelayAdv (toSys r) (toSys r′)
τreflect-relay r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-relay r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-relay r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-relay r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with the relay report (mirror `PipeExposeNodeProd.liftτ*-prod`).
------------------------------------------------------------------------

liftτ*-relay′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllRelayAdv (toSys r) (toSys r′)
liftτ*-relay′ r eq τ*-refl = r , eq , allRelayAdv-refl (toSys r)
liftτ*-relay′ r eq (τ*-step s rest) with τreflect-relay r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , rep₁ with liftτ*-relay′ r₁ eq₁ rest
...   | r′ , equ , rep′ =
        r′ , equ , allRelayAdv-trans (toSys r) (toSys r₁) (toSys r′) rep₁ rep′

liftτ*-relay : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllRelayAdv (toSys r) (toSys r′)
liftτ*-relay r = liftτ*-relay′ r refl

------------------------------------------------------------------------
-- The leg-`l` `RelayReport`: instantiate `AllRelayAdv` at the leg's relay driver
-- (`relayOf`) — the RELAY component of the seven-component `PipeReport`.
------------------------------------------------------------------------

-- how the leg-`l` relay driver moves across a τ-run
RelayReport : TwoLegs → SysState → SysState → Set
RelayReport l s s′ = RelayAdv (relayOf l s) (relayOf l s′)

-- project the whole-nodes report onto the leg relay
allRelayAdv⇒RelayReport : (l : TwoLegs) (s s′ : SysState)
                        → AllRelayAdv s s′ → RelayReport l s s′
allRelayAdv⇒RelayReport legBD s s′ (uBD , uCD) = uBD
allRelayAdv⇒RelayReport legCD s s′ (uBD , uCD) = uCD

-- HEADLINE (τ-run half of the leg `RelayReport`): a hidden τ-run exposes the
-- leg-`l` relay driver's phase delta (a `RelayAdv`, forwarded-gate flagged)
liftτ*-relayReport : (l : TwoLegs) (r : RState) {u : NetProc}
                   → radec r ─[τ*]─► u
                   → Σ[ r′ ∈ RState ] (u ≡ radec r′) × RelayReport l (toSys r) (toSys r′)
liftτ*-relayReport l r run with liftτ*-relay r run
... | r′ , eq , arr = r′ , eq , allRelayAdv⇒RelayReport l (toSys r) (toSys r′) arr

------------------------------------------------------------------------
-- The strong-visible api middle WITH the relay report on the SAME `r′` (mirror
-- `PipeExposeNodeProd.reach-ev-prod`, but for the relay driver).  Reuses
-- `reach-ev-both`'s reflected successor `r′` and reads `AllRelayAdv` off it via
-- the total `allRelayAdv-of` — no per-peer node cone.
------------------------------------------------------------------------

reach-ev-relay : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × AllRelayAdv (toSys r) (toSys r′)
reach-ev-relay r aic apimem step with reach-ev-both r aic apimem step
... | r′ , Mr , wr , drop , _ , _ = r′ , Mr , wr , drop , allRelayAdv-of (toSys r) (toSys r′)

-- the leg-`l` projection of the visible-middle relay frame
reach-ev-relayReport : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × RelayReport l (toSys r) (toSys r′)
-- NB `let`-destructuring, NOT `with`: in this `(blkA : Block₃)`-parameterised
-- module a `with` abstracts the block out of the imported `PipeInv.relayOf`
-- copy and the abstracted goal stops converting.
reach-ev-relayReport l r aic apimem step =
  let (r′ , Mr , wr , drop , arr) = reach-ev-relay r aic apimem step
  in  r′ , Mr , wr , drop , allRelayAdv⇒RelayReport l (toSys r) (toSys r′) arr

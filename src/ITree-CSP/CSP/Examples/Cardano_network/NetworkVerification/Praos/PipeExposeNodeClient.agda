{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the NODE BF-CLIENT exposure cone + τ-run
-- (`Praos.PipeExposeNodeClient`).
--
-- The MEDIUM companion `PipeExposeCell` exposes, across a hidden τ-run, how the
-- leg cells move (`AllCellAdv`, from `medium-ev-inv-wt`'s `setCell` form).  This
-- module is the NODE counterpart: how the leg's BF-CLIENT peers advance across
-- the same τ-paddings (`ClientAdv`, from `PipeExposeNode`).
--
-- KEY SIMPLIFICATION of the session-7 recipe.  The recipe planned a full
-- per-peer 4×12 bundle-threading cone (`absBundleG-io-client-adv` +
-- `nodeD-io-*-abs-client` + `top-nodes-io-abs-client`) to surface the fired
-- peer's `ClientAdv`.  But `PipeExposeNode.adv-of : (q q′) → ClientAdv q q′` is
-- TOTAL (session-7's own key finding: the BF-client phase can't be
-- weight-classified, so the advance is read off the CONCRETE successor phase).
-- Since `WalkConvNodeFix.top-nodes-io-abs-fix` ALREADY reflects the io-sync to a
-- successor state `s′` carrying the peers' concrete new phases, the `ClientAdv`
-- reads DIRECTLY off `s′` via `adv-of` — no per-peer bundle threading is needed.
-- Hence `top-nodes-io-abs-client` is a thin wrapper over the frozen
-- `top-nodes-io-abs-fix`, and the RAM cost is that of the io-sync reflection
-- only (≈ `PipeExposeCell.τreflect-io-cell`), not a fresh 4×12 cone.
--
-- No postulate/hole/meta.  All base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeNodeClient (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p )
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
  using ( upClient; dnClient )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeNode blkA
  using ( ClientAdv; cl-refl; cl-step; cl-trans; adv-of )

------------------------------------------------------------------------
-- The whole-nodes client report `AllClientAdv`: a `ClientAdv` for EACH of the
-- four `PipeInv`-tracked BF-client peers (the two legs' upstream + downstream
-- clients — `bfC-AB`/`bfC-AC` on nodes B/C, `bfC-BD`/`bfC-CD` on node D).  This
-- is the client analogue of `PipeExposeCell.AllCellAdv`; it composes pointwise
-- and refl-everywhere for a nodes-fixed step (the frame case).
------------------------------------------------------------------------

-- the four tracked BF-client peers advance together
AllClientAdv : SysState → SysState → Set
AllClientAdv s s′ =
    ClientAdv (upClient legBD s) (upClient legBD s′)
  × ClientAdv (upClient legCD s) (upClient legCD s′)
  × ClientAdv (dnClient legBD s) (dnClient legBD s′)
  × ClientAdv (dnClient legCD s) (dnClient legCD s′)

-- reflexivity: a nodes-fixed step keeps every tracked client (the frame case)
allClientAdv-refl : (s : SysState) → AllClientAdv s s
allClientAdv-refl s = cl-refl , cl-refl , cl-refl , cl-refl

-- transitivity (pointwise): compose two client reports across a τ-run
allClientAdv-trans : (s s₁ s₂ : SysState)
                   → AllClientAdv s s₁ → AllClientAdv s₁ s₂ → AllClientAdv s s₂
allClientAdv-trans s s₁ s₂ (u₁ , v₁ , w₁ , x₁) (u₂ , v₂ , w₂ , x₂) =
    cl-trans u₁ u₂ , cl-trans v₁ v₂ , cl-trans w₁ w₂ , cl-trans x₁ x₂

-- TOTAL classify: any successor state yields an `AllClientAdv`, reading each
-- tracked client's `ClientAdv` off the concrete successor phase (`adv-of`).
-- This is what makes the per-peer bundle-threading cone unnecessary.
allClientAdv-of : (s s′ : SysState) → AllClientAdv s s′
allClientAdv-of s s′ =
    adv-of (upClient legBD s) (upClient legBD s′)
  , adv-of (upClient legCD s) (upClient legCD s′)
  , adv-of (dnClient legBD s) (dnClient legBD s′)
  , adv-of (dnClient legCD s) (dnClient legCD s′)

------------------------------------------------------------------------
-- TOP: the whole-nodes io-sync BF-CLIENT exposure (`top-nodes-io-abs-client`,
-- recipe (c)).  A thin wrapper over the frozen `top-nodes-io-abs-fix`: it
-- reuses the reflected successor state `s′`, the `med`-fixity, the
-- `M ≡ absNodesOf s′` equation and the `nodesOf` weak run VERBATIM, and
-- attaches the `AllClientAdv` read off `s′` via the total `allClientAdv-of`
-- (the six driver fixities `top-nodes-io-abs-fix` also exposes are discarded).
------------------------------------------------------------------------

top-nodes-io-abs-client : (s : SysState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × AllClientAdv s s′
top-nodes-io-abs-client s iomem step with top-nodes-io-abs-fix s iomem step
... | s′ , meq , Meq , wrun , _ , _ , _ , _ , _ , _ =
      s′ , meq , Meq , wrun , allClientAdv-of s s′

------------------------------------------------------------------------
-- MEDIUM-τ reflector with the client report (mirror
-- `PipeExposeCell.τreflect-med-cell`, LIGHT — medium-only τ lift): a medium
-- drain moves NO node, so every tracked client is fixed (`allClientAdv-refl`).
------------------------------------------------------------------------

τreflect-med-client : (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllClientAdv (toSys r) (toSys r′)
τreflect-med-client r {M} {M′} ms Meq with medium-τ-inv-wt (med (toSys r)) ms
... | i , d₀ , id₀ , _ , _ , M′≡ = r′ , Meq′ , allClientAdv-refl (toSys r)
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
-- io-SYNC reflector with the client report (RAM-heavy — mirror
-- `PipeExposeCell.τreflect-io-cell`, but using `top-nodes-io-abs-client` for the
-- node side so the reflected successor's tracked clients advance).  The medium
-- side (setting one cell) is rebuilt through `lift-io-sync-whole-wτ` exactly as
-- the frozen cell module does; the client report comes off the reflected `s″`.
------------------------------------------------------------------------

τreflect-io-client : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
    (iomem : ioES .mem (X , e) a)
    (sM : decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁)
    (sN : absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁)
    (Meq : M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllClientAdv (toSys r) (toSys r′)
τreflect-io-client r {X} {e} {a} {M₁} {N₁} {M} iomem sM sN Meq
    with medium-ev-inv-wt (med (toSys r)) iomem sM
       | top-nodes-io-abs-client (toSys r) iomem sN
... | i , d₀ , id₀ , np , _ , M₁≡ | s″ , _ , N₁≡ , cWeakRun , clientRep =
      r′ , Meq′ , clientRep
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
-- TOTAL per-τ reflector with the client report (mirror
-- `PipeExposeCell.τreflect-cell`): dispatch a hidden τ to the medium-τ drain
-- reflector or the io-sync reflector (nodes-τ is refuted by `absNodesOf-no-τ`).
------------------------------------------------------------------------

τreflect-client : (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × AllClientAdv (toSys r) (toSys r′)
τreflect-client r step with reflect-absDec-τ (toSys r) step
... | innerτ P′ innerStep Peq
    with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
...   | medτ   M′ ms eqP = τreflect-med-client r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
τreflect-client r step | hidSync M₁ N₁ iomem sM sN Peq = τreflect-io-client r iomem sM sN Peq

------------------------------------------------------------------------
-- τ-run lift with the client report (mirror `PipeExposeCell.liftτ*-cell`): fold
-- the per-τ client reports across a whole hidden τ-run by pointwise `ClientAdv`
-- composition.  This is the τ-run half of the leg-`l` `ClientReport`.
------------------------------------------------------------------------

liftτ*-client′ : (r : RState) {start u : NetProc} → start ≡ radec r
          → start ─[τ*]─► u
          → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllClientAdv (toSys r) (toSys r′)
liftτ*-client′ r eq τ*-refl = r , eq , allClientAdv-refl (toSys r)
liftτ*-client′ r eq (τ*-step s rest) with τreflect-client r (subst (λ z → z ─[ τ ]─► _) eq s)
... | r₁ , eq₁ , rep₁ with liftτ*-client′ r₁ eq₁ rest
...   | r′ , equ , rep′ =
        r′ , equ , allClientAdv-trans (toSys r) (toSys r₁) (toSys r′) rep₁ rep′

liftτ*-client : (r : RState) {u : NetProc}
         → radec r ─[τ*]─► u
         → Σ[ r′ ∈ RState ] (u ≡ radec r′) × AllClientAdv (toSys r) (toSys r′)
liftτ*-client r = liftτ*-client′ r refl

------------------------------------------------------------------------
-- The leg-`l` `ClientReport`: instantiate `AllClientAdv` at the leg's upstream
-- and downstream BF-client peers (`upClient`/`dnClient`) — the CLIENT component
-- of the seven-component `PipeReport`, the node counterpart of `CellReport`.
------------------------------------------------------------------------

-- how the leg-`l` upstream + downstream BF-client peers move across a τ-run
ClientReport : TwoLegs → SysState → SysState → Set
ClientReport l s s′ = ClientAdv (upClient l s) (upClient l s′) × ClientAdv (dnClient l s) (dnClient l s′)

-- project the whole-nodes report onto the two leg clients
allClientAdv⇒ClientReport : (l : TwoLegs) (s s′ : SysState)
                          → AllClientAdv s s′ → ClientReport l s s′
allClientAdv⇒ClientReport legBD s s′ (uBD , uCD , dBD , dCD) = uBD , dBD
allClientAdv⇒ClientReport legCD s s′ (uBD , uCD , dBD , dCD) = uCD , dCD

-- HEADLINE (τ-run half of the leg `ClientReport`): a hidden τ-run exposes the
-- leg-`l` BF-client peers' phase deltas (each a `ClientAdv`, block-gain flagged)
liftτ*-clientReport : (l : TwoLegs) (r : RState) {u : NetProc}
                    → radec r ─[τ*]─► u
                    → Σ[ r′ ∈ RState ] (u ≡ radec r′) × ClientReport l (toSys r) (toSys r′)
liftτ*-clientReport l r run with liftτ*-client r run
... | r′ , eq , acr = r′ , eq , allClientAdv⇒ClientReport l (toSys r) (toSys r′) acr

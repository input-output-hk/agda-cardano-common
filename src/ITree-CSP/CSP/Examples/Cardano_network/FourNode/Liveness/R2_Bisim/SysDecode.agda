{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R1 — WHOLE-SYSTEM decode (`Praos.SysDecode`), Task 4 (HEADLINE).
--
-- The assembly of the three genuine sub-decodes (Tasks 1–3) into the whole
-- diamond decode `⟦_⟧ : SysState → NetProc` and the GENUINE
-- `dec-init : ⟦ initial ⟧ ≡ systemBroken` — R1's whole point.  In the R2 spike
-- (`Route2Spike`) this equality was a POSTULATED stand-in (`decNodes`/
-- `decNodes-home` were abstract fields); here it is made real: `decMed` comes
-- from `SysMedium`, the four node decodes from `SysNode`, and `dec-init` is a
-- genuine `cong₂`-glue over the `(_ ∥⇘ ioES ⇙ _) ∖ ioES` skeleton fed by the
-- five genuine home-equalities (`decMed-home` + the four `decNodeX-home`).
--
-- `systemBroken` (FourNodeDiamondBroken.76) is
--   (CopySpecBreakableA ∥⇘ ioES ⇙ (nodeA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))) ∖ ioES
-- and `⟦_⟧` rebuilds EXACTLY this shape, substituting each sub-decode at its
-- state and MATCHING the node `⦀` association `nodeA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD))`.
--
-- Q1 (make-or-break) confirmation on the REAL assembled decode: `dec-init` is
-- `cong₂`-glue.  `cong₂ f p q` (and the nested `cong₂ _⦀_` on the node side)
-- produces `f _ _ ≡ f _ _` WITHOUT forcing `f` to WHNF, so the `∥⇘ ioES ⇙` /
-- `∖ ioES` / node-`⦀` composite tree is NEVER evaluated — the typecheck stays
-- in seconds, dodging the 2.5-min/20-GB WHNF wall the spike identified.
--
-- No postulates, holes, or `--allow-unsolved-metas` (R1 must be genuine).
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode (blkA : Block₃) where

------------------------------------------------------------------------
-- The concrete model under study (Phase-1, `examples/praos_liveness`).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; nodeA; nodeB; nodeC; nodeD )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBroken
  using ( systemBroken )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

-- Net_Api operators (the whole-system alphabet): the top io-gated stack + node ⦀
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_ )

-- the three genuine sub-decodes (Tasks 1–3)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; decMed; initMed; decMed-home )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( NodeStateA; NodeStateB; NodeStateC; NodeStateD
        ; decNodeA; decNodeB; decNodeC; decNodeD
        ; initNodeA; initNodeB; initNodeC; initNodeD
        ; decNodeA-home; decNodeB-home; decNodeC-home; decNodeD-home )

-- the whole-system process type (same alias as the spike / `systemBroken`)
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

------------------------------------------------------------------------
-- The whole-diamond abstract state and its decode.
------------------------------------------------------------------------

-- the whole-diamond abstract state: the medium cells plus the four nodes'
-- joint-FSM positions (the inert peers contribute no state component)
record SysState : Set where
  constructor mkSys
  field
    med : MedState
    nA  : NodeStateA
    nB  : NodeStateB
    nC  : NodeStateC
    nD  : NodeStateD
open SysState public

-- the whole-system decode, rebuilding `systemBroken`'s
-- `(medium ∥⇘ ioES ⇙ (nodeA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))) ∖ ioES` shape from
-- the medium sub-decode and the four node sub-decodes (same `⦀` association)
⟦_⟧ : SysState → NetProc
⟦ s ⟧ =
  (decMed (med s)
    ∥⇘ ioES ⇙
    (decNodeA (nA s) ⦀ (decNodeB (nB s) ⦀ (decNodeC (nC s) ⦀ decNodeD (nD s)))))
  ∖ ioES

-- the initial (all-home / unbroken) whole-system state
initial : SysState
initial = mkSys initMed initNodeA initNodeB initNodeC initNodeD

------------------------------------------------------------------------
-- Q1 MAKE-OR-BREAK RESULT — the genuine whole-system home-equality.
------------------------------------------------------------------------

-- GENUINE `dec-init`: a `cong₂`-glue through the `∖ ioES` / `∥⇘ ioES ⇙` stack,
-- with the node side glued by a nested `cong₂ _⦀_` over the four node ⦀s.  Fed
-- by the five genuine home-equalities; `cong₂`/`cong` never force the composite
-- to WHNF, so the typecheck stays in seconds (no 2.5-min/20-GB WHNF wall).
dec-init : ⟦ initial ⟧ ≡ systemBroken blkA
dec-init =
  cong₂ (λ Md Nd → (Md ∥⇘ ioES ⇙ Nd) ∖ ioES)
    decMed-home
    (cong₂ _⦀_ decNodeA-home
      (cong₂ _⦀_ decNodeB-home
        (cong₂ _⦀_ decNodeC-home decNodeD-home)))

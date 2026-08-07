{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — `tprog` via the sanctioned campaign `dne`
-- (`Praos.TProg`).
--
-- `RealAbs`'s single residual obligation is the abstract-τ-enabledness
-- DECISION
--
--   tprog : (r : RState) → τ-progress (radec r)
--
-- with `τ-progress t = (Σ t′. t ─[τ]─► t′) ⊎ (∀ {t′}. t ─[τ]─► t′ → ⊥)`
-- (`Semantics.LTL.Convergence`).  This is a pure `P ⊎ ¬ P` instance at
-- `P = Σ t′. radec r ─[τ]─► t′` — the excluded middle, which the campaign
-- already sanctions via the single `Classical.dne` axiom (the same axiom
-- `respondsᵂ-intro` / `descent-⊨` rest on).  Deriving `em = P ⊎ ¬ P` from
-- `dne` and re-packaging the negative disjunct (its implicit-`{t′}` shape)
-- closes `tprog` in one line.  No forward τ-inversion, no oracle-scale cone.
------------------------------------------------------------------------

open import Data.Empty using ( ⊥ )
open import Data.Product using ( Σ; Σ-syntax; _,_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )

open import Process_Trees using ( PTree; ExtI )

open import Classical using ( dne )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.TProg (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ )
open import Semantics.LTL.Convergence {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( τ-progress )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; radec )

-- excluded middle from the sanctioned double-negation-elimination axiom
em : ∀ {ℓa} {A : Set ℓa} → A ⊎ (A → ⊥)
em = dne (λ k → k (inj₂ (λ p → k (inj₁ p))))

-- the abstract-τ-enabledness decision, at every reachable config decode: a
-- pure `P ⊎ ¬ P` instance, re-packaging the negative disjunct's implicit `{t′}`
tprog : (r : RState) → τ-progress (radec r)
tprog r with em {A = Σ[ t′ ∈ _ ] (radec r ─[ τ ]─► t′)}
... | inj₁ p  = inj₁ p
... | inj₂ np = inj₂ (λ step → np (_ , step))

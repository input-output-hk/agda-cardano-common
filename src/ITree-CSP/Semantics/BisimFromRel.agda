{-# OPTIONS --guardedness #-}

-- Relation → bisimulation coinduction principles, model-generic.
-- `DRFromRel` turns a step-matching, divergence-free relation into `≈DR`;
-- `WSimFromRel` is its forward-only half producing `WSim`.  Hoisted from the
-- five CSP.Examples.TPC modules (previously six byte-identical copies).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

open import Process_Trees

module Semantics.BisimFromRel {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.LTS       {E = E} {I = I} hiding (Diverges)
open import Semantics.WeakBisim {E = E} {I = I}
open import Semantics.WeakSim   {E = E} {I = I}
open import Semantics.DRBisim   {E = E} {I = I}
open WSimF

module DRFromRel
  {ℓr} {R : Set ℓr} {ℓR}
  (Rel  : PTree E I R → PTree E I R → Set ℓR)
  (fwdE : ∀ {p q} {l : Event√ R} {p′} → Rel p q → p ─[ ev l ]─► p′
        → Σ[ q′ ∈ PTree E I R ] ((q ═[ ev l ]═► q′) × Rel p′ q′))
  (fwdT : ∀ {p q p′} → Rel p q → p ─[ τ ]─► p′
        → Σ[ q′ ∈ PTree E I R ] ((q ═[ τ ]═► q′) × Rel p′ q′))
  (bwdE : ∀ {p q} {l : Event√ R} {q′} → Rel p q → q ─[ ev l ]─► q′
        → Σ[ p′ ∈ PTree E I R ] ((p ═[ ev l ]═► p′) × Rel p′ q′))
  (bwdT : ∀ {p q q′} → Rel p q → q ─[ τ ]─► q′
        → Σ[ p′ ∈ PTree E I R ] ((p ═[ τ ]═► p′) × Rel p′ q′))
  (ndivL : ∀ {p q} → Rel p q → Diverges p → ⊥)
  (ndivR : ∀ {p q} → Rel p q → Diverges q → ⊥)
  where

  rel→dr : ∀ {p q} → Rel p q → p ≈DR q
  rel→rd : ∀ {p q} → Rel p q → q ≈DR p

  rel→dr r .DRbisim.fwd .on-ev stp with fwdE r stp
  ... | q′ , w , r′ = q′ , w , rel→dr r′
  rel→dr r .DRbisim.fwd .on-tau stp with fwdT r stp
  ... | q′ , w , r′ = q′ , w , rel→dr r′
  rel→dr r .DRbisim.bwd .on-ev stp with bwdE r stp
  ... | p′ , w , r′ = p′ , w , rel→rd r′
  rel→dr r .DRbisim.bwd .on-tau stp with bwdT r stp
  ... | p′ , w , r′ = p′ , w , rel→rd r′
  rel→dr r .DRbisim.div→ d = ⊥-elim (ndivL r d)
  rel→dr r .DRbisim.div← d = ⊥-elim (ndivR r d)

  rel→rd r .DRbisim.fwd .on-ev stp with bwdE r stp
  ... | p′ , w , r′ = p′ , w , rel→rd r′
  rel→rd r .DRbisim.fwd .on-tau stp with bwdT r stp
  ... | p′ , w , r′ = p′ , w , rel→rd r′
  rel→rd r .DRbisim.bwd .on-ev stp with fwdE r stp
  ... | q′ , w , r′ = q′ , w , rel→dr r′
  rel→rd r .DRbisim.bwd .on-tau stp with fwdT r stp
  ... | q′ , w , r′ = q′ , w , rel→dr r′
  rel→rd r .DRbisim.div→ d = ⊥-elim (ndivR r d)
  rel→rd r .DRbisim.div← d = ⊥-elim (ndivL r d)

module WSimFromRel
  {ℓr} {R : Set ℓr} {ℓR}
  (Rel  : PTree E I R → PTree E I R → Set ℓR)
  (fwdE : ∀ {p q} {l : Event√ R} {p′} → Rel p q → p ─[ ev l ]─► p′
        → Σ[ q′ ∈ PTree E I R ] ((q ═[ ev l ]═► q′) × Rel p′ q′))
  (fwdT : ∀ {p q p′} → Rel p q → p ─[ τ ]─► p′
        → Σ[ q′ ∈ PTree E I R ] ((q ═[ τ ]═► q′) × Rel p′ q′))
  where

  rel→wsim : ∀ {p q} → Rel p q → WSim R p q
  rel→wsim r .fwd .on-ev stp with fwdE r stp
  ... | q′ , w , r′ = q′ , w , rel→wsim r′
  rel→wsim r .fwd .on-tau stp with fwdT r stp
  ... | q′ , w , r′ = q′ , w , rel→wsim r′

{-# OPTIONS --guardedness #-}

-- Strong bisimulation implies divergence-respecting weak bisimulation.
-- A strong step is matched one-for-one, so (a) it weakens to a τ*-padded weak step,
-- and (b) an infinite τ-path is mapped to an infinite τ-path — i.e. divergence is
-- preserved exactly.  Composing with `drbisim→≈FD` turns every STRONG-bisim CSP law
-- (e.g. ⊓-commutativity) into an ≈FD law for free.

open import Data.Product using (_,_; proj₁; proj₂)

open import Process_Trees

module Semantics.StrongImpliesDR
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I} hiding (Diverges)
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.DRBisim   {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Bisim     {ℓ} {ℓe} {ℓi} {E} {I}

-- strong bisimulation preserves divergence (single-step matching keeps the τ-path infinite)
-- copattern form (no top-level `with`) so the corecursive call sits under the
-- `.Diverges.rest` projection and is recognised as productive
sbisim-div→ : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
            → Sbisim R t₁ t₂ → Diverges t₁ → Diverges t₂
sbisim-div→ s d .Diverges.next =
  proj₁ (s .Sbisim.fwd .SSimF.on-tau (d .Diverges.step))
sbisim-div→ s d .Diverges.step =
  proj₁ (proj₂ (s .Sbisim.fwd .SSimF.on-tau (d .Diverges.step)))
sbisim-div→ s d .Diverges.rest =
  sbisim-div→ (proj₂ (proj₂ (s .Sbisim.fwd .SSimF.on-tau (d .Diverges.step))))
              (d .Diverges.rest)

sbisim→drbisim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
               → Sbisim R t₁ t₂ → DRbisim R t₁ t₂
sbisim→drbisim s .DRbisim.fwd .WSimF.on-ev  evstep with s .Sbisim.fwd .SSimF.on-ev evstep
... | _ , step , s′ = _ , wev τ*-refl step τ*-refl , sbisim→drbisim s′
sbisim→drbisim s .DRbisim.fwd .WSimF.on-tau tstep with s .Sbisim.fwd .SSimF.on-tau tstep
... | _ , step , s′ = _ , wτ (τ*-step step τ*-refl) , sbisim→drbisim s′
sbisim→drbisim s .DRbisim.bwd .WSimF.on-ev  evstep with s .Sbisim.bwd .SSimF.on-ev evstep
... | _ , step , s′ = _ , wev τ*-refl step τ*-refl , sbisim→drbisim s′
sbisim→drbisim s .DRbisim.bwd .WSimF.on-tau tstep with s .Sbisim.bwd .SSimF.on-tau tstep
... | _ , step , s′ = _ , wτ (τ*-step step τ*-refl) , sbisim→drbisim s′
sbisim→drbisim s .DRbisim.div→ d = sbisim-div→ s d
sbisim→drbisim s .DRbisim.div← d = sbisim-div→ (sbisim-sym s) d

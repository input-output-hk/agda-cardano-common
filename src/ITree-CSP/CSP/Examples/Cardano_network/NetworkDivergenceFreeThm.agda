{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Divergence-freedom for the Cardano `Network` example.
--
-- Ports the generic CopySpec non-divergence invariant (`GoodC` /
-- `copy-reach-noDiv`) — reusing the C0/C1/Cg step characterizations and
-- ¬Diverges lemmas that already exist in `NetworkRefinementGen` — to obtain
-- `DivergenceFree CopySpec`, then transfers it across the master DR-bisim key
-- `net≈DR` (from `NetworkRefinementGenExp`) via the generic trivial transfer
-- `drbisim-divergenceFree`, delivering `DivergenceFree Network`.
------------------------------------------------------------------------

open import Class.DecEq using (DecEq)
open import Process_Trees using (ExtI)

module CSP.Examples.Cardano_network.NetworkDivergenceFreeThm
  (Data : Set) ⦃ _ : DecEq Data ⦄ (d₀ : Data) where

-- Reuse every Step-0/1 definition + the C0/C1/Cg lemmas from the Gen module.
open import CSP.Examples.Cardano_network.NetworkRefinementGen Data
  using ( p1
        ; NetR
        ; C0; C1; Cg
        ; ¬Div-C0; ¬Div-C1; ¬Div-Cg
        ; C0-noτ; C1-noτ; Cg-τ; Cg-noev
        ; C0-evL; C1-evL
        ; ≟-diag )

-- Bring Net into scope (for the Semantics.* instantiations).
open import CSP.Examples.Cardano_network.Net p1 using (Net)

-- Master key: Network ≈DR CopySpec over p1.
open import CSP.Examples.Cardano_network.NetworkRefinementGenExp Data using (net≈DR)

-- `Network` and `CopySpec` both come from the SAME `Network p1 Data` open.
open import CSP.Examples.Cardano_network.Network p1 Data using (Network; NetProc; CopySpec)

-- Generic divergence-freedom predicate + its trivial ≈DR transfer.
open import Semantics.DeadlockDR {E = Net Data} {I = ExtI (Net Data)}
  using (DivergenceFree; drbisim-divergenceFree)

-- A √-free run embeds into the general big-step run.
open import Semantics.Deadlock {E = Net Data} {I = ExtI (Net Data)}
  using (embed∖√)

-- Weak-reach big-step relation and its constructors.
open import Semantics.Failures {E = Net Data} {I = ExtI (Net Data)}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)

-- Divergence predicate.
open import Semantics.DRBisim {E = Net Data} {I = ExtI (Net Data)}
  using (Diverges)

-- LTS labels / steps.
open import Semantics.LTS {E = Net Data} {I = ExtI (Net Data)}
  using (_─[_]─►_; τ; ev; evl; √; Event√; sRet)

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)

------------------------------------------------------------------------
-- Coinductive divergence-freedom invariant.  `gcev` is stated for ANY
-- `ev e` (an `evl` visible event OR a `√` termination), so the reach-walk can
-- consume any `⟹-ev`.
------------------------------------------------------------------------
record GoodC (W : NetProc) : Set₁ where
  coinductive
  field
    gcnd : ¬ Diverges W
    gcτ  : ∀ {W′} → W ─[ τ ]─► W′ → GoodC W′
    gcev : ∀ {W′} {e : Event√ NetR} → W ─[ ev e ]─► W′ → GoodC W′
open GoodC

-- The three CopySpec lifecycle states are good.  A `√` step is refuted
-- (`sRet ()` — every state is react-headed, force ≢ ret); an `evl` step is
-- routed by the per-state event characterization.  `with`-matching the
-- `≡`-lemma to `refl` keeps the corecursive call directly under the copattern
-- (productive), mirroring the concrete template.
goodC-C0 : GoodC C0
goodC-C1 : ∀ d → GoodC (C1 d)
goodC-Cg : ∀ d → GoodC (Cg d)

goodC-C0 .gcnd                 = ¬Div-C0
goodC-C0 .gcτ  st              = ⊥-elim (C0-noτ st)
goodC-C0 .gcev {e = √ x}    (sRet ())
goodC-C0 .gcev {e = evl _} st  with C0-evL st
... | d , _ , eq  rewrite eq    = goodC-C1 d

goodC-C1 d .gcnd                 = ¬Div-C1
goodC-C1 d .gcτ  st              = ⊥-elim (C1-noτ st)
goodC-C1 d .gcev {e = √ x}    (sRet ())
goodC-C1 d .gcev {e = evl _} st  with C1-evL st
... | _ , eq  rewrite eq         = goodC-Cg d

goodC-Cg d .gcnd                 = ¬Div-Cg
goodC-Cg d .gcτ  st              with Cg-τ st
... | eq  rewrite eq             = goodC-C0
goodC-Cg d .gcev {e = √ x}    st  rewrite ≟-diag d  with st
... | sRet ()
goodC-Cg d .gcev {e = evl _} st  = ⊥-elim (Cg-noev st)

------------------------------------------------------------------------
-- No weakly-reachable state of CopySpec diverges.
------------------------------------------------------------------------

-- `C0 = CopySpec`, so `goodC-C0 : GoodC CopySpec`.
copy-reach-noDiv : ∀ {s W} → CopySpec ⟹⟨ s ⟩ W → ¬ Diverges W
copy-reach-noDiv = go goodC-C0
  where
  go : ∀ {s W W′} → GoodC W → W ⟹⟨ s ⟩ W′ → ¬ Diverges W′
  go g ⟹-refl         = g .gcnd
  go g (⟹-τ  st rest) = go (g .gcτ  st) rest
  go g (⟹-ev st rest) = go (g .gcev st) rest

------------------------------------------------------------------------
-- Final theorems.
------------------------------------------------------------------------

-- CopySpec is divergence-free: embed the √-free run into `⟹⟨⟩`, apply the
-- reach-walk non-divergence.
DivergenceFree-CopySpec : DivergenceFree CopySpec
DivergenceFree-CopySpec reach div = copy-reach-noDiv (embed∖√ reach) div

-- Network is divergence-free: transfer across the master key net≈DR.
Network-divergenceFree : DivergenceFree Network
Network-divergenceFree = drbisim-divergenceFree (net≈DR d₀) DivergenceFree-CopySpec

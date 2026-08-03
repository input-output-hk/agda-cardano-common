{-# OPTIONS --guardedness #-}

-- SMOKE TEST for `Semantics.FailureSim` / `Semantics.BisimFromRel.FSimFromRel`.
--
-- `CSP.Examples.UCS.Ch6.Buffers` proves `copy-is-buff1 : BUFFN1 ≈FD COPY` by building a
-- full `≈DR` through `DRFromRel` (SIX obligations) and applying `drbisim→≈FD`.  Since
-- `P ≈FD Q = (P ⊑FD Q) × (Q ⊑FD P)`, its SECOND component is `COPY ⊑FD BUFFN1` — the
-- "spec ⊑FD impl" half, with COPY as the specification.
--
-- Here we obtain exactly that half through the ONE-WAY route: `FSimFromRel` reuses
-- Buffers' relation `BRel` and its FORWARD obligations `fwdE`/`fwdT`/`ndivL` VERBATIM,
-- and adds one stability/offer-inclusion obligation.  `bwdE`, `bwdT` and `ndivR` (the
-- backward simulation and the spec-side divergence-freedom) are NEVER mentioned, which
-- is the point: they are dead weight for a refinement.
--
-- `orientation-check` below pins the direction claim mechanically: it typechecks the
-- FSim-derived refinement against the `proj₂` of the existing `≈FD` result.

module CSP.Examples.UCS.Ch6.BuffersFSim where

open import Level renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-- reuse the process definitions, the relation and the FORWARD obligations
open import CSP.Examples.UCS.Ch6.Buffers

open import Semantics.LTS        {E = BEv} {I = ExtI BEv}
open import Semantics.WeakBisim  {E = BEv} {I = ExtI BEv} using (_─[τ*]─►_; τ*-refl)
open import Semantics.Refusals   {E = BEv} {I = ExtI BEv} using (Offers)
open import Semantics.FailureSim {E = BEv} {I = ExtI BEv} using (FSim; fsim→⊑FD)
open import Semantics.FailuresDivergences {E = BEv} {I = ExtI BEv} using (_⊑FD_)
open import Semantics.BisimFromRel {E = BEv} {I = ExtI BEv} using (module FSimFromRel)
-- the divergence-freedom calculus: `stable→¬div` is all the `ndivL` obligation needs
open import Semantics.DivergenceFree {E = BEv} {I = ExtI BEv} using (stable→¬div)

-- Offer reflection: every visible offer of the SPEC side (COPY / COPYout) is also
-- offered by the IMPL side (BUFN 1).  This is all the "backward" information a failures
-- refinement needs — a single-step offer witness, with no residual relation and no
-- weak (τ*-padded) matching, unlike `DRFromRel`'s `bwdE`.
brel-reflect : ∀ {p q} {e : Event√ (⊤poly {lzero})} → BRel p q → Offers q e → Offers p e
brel-reflect rel-empty    (_ , sRet ())
brel-reflect rel-empty    (_ , sVis {at = _ , right} refl ())
brel-reflect rel-empty    (_ , sVis {at = _ , left} {a = x} refl refl) =
  BUFN 1 (x ∷ []) , bufn-in-fire x
brel-reflect (rel-full x) (_ , sRet ())
brel-reflect (rel-full x) (_ , sVis {at = _ , left} refl ())
brel-reflect (rel-full x) (_ , sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes e = BUFN 1 [] , bufn-out-fire x e
... | no  _ = case br of λ ()

-- The `FSimFromRel` stability obligation: both spec states are already stable
-- (`react … ∅t`), so no τ*-settling is needed and the offers reflect by the above.
brel-stab : ∀ {p q} → BRel p q → isStable p
          → Σ[ q′ ∈ BProc ]
              ( (q ─[τ*]─► q′) × isStable q′
              × (∀ (e : Event√ (⊤poly {lzero})) → Offers q′ e → Offers p e) )
brel-stab rel-empty    _ = COPY      , τ*-refl , (λ _ _ → refl) , λ _ off → brel-reflect rel-empty off
brel-stab (rel-full x) _ = COPYout x , τ*-refl , (λ _ _ → refl) , λ _ off → brel-reflect (rel-full x) off

-- The `FSimFromRel` non-divergence obligation, discharged through the divergence-freedom
-- calculus instead of by hand: both IMPL states are `react … ∅t` nodes, so `isStable`
-- reduces to `λ _ _ → refl` and `stable→¬div` closes each case.  `Buffers` spells the
-- same fact out as a five-clause `noτ-L` τ-step inversion plus a two-line `ndivL`.
brel-ndivL : ∀ {p q} → BRel p q → Diverges p → ⊥
brel-ndivL rel-empty    = stable→¬div (λ _ _ → refl)
brel-ndivL (rel-full x) = stable→¬div (λ _ _ → refl)

open FSimFromRel BRel fwdE fwdT brel-stab brel-ndivL

-- COPY failure-simulates BUFFN1 (impl BUFFN1 on the left, spec COPY on the right)
buff1-fsim-copy : FSim (⊤poly {lzero}) BUFFN1 COPY
buff1-fsim-copy = rel→fsim rel-empty

-- the one-way half of `copy-is-buff1`, via FSim only
copy⊑FD-buff1 : COPY ⊑FD BUFFN1
copy⊑FD-buff1 = fsim→⊑FD buff1-fsim-copy

-- mechanical confirmation that this really is the second component of `BUFFN1 ≈FD COPY`
orientation-check : COPY ⊑FD BUFFN1
orientation-check = proj₂ copy-is-buff1

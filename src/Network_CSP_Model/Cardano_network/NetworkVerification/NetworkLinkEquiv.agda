{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — headline equivalence between the LINK-INDEXED
-- `NetworkLink` (`NetworkLink.agda`) and the CSPm `CopySpec` bundle
-- (`Network.agda`, `CopySpec = ⦀Fin numLinks linkCopy` definitionally).
--
-- The proof is a single application of `cong-⦀Fin` (the `⦀Fin`-congruence
-- of `DRCongruenceRep`) fed by `linkAlpha`/`linkAlpha-disj` and the two
-- `OffersOnly` confinement results of `NetworkLinkOffers`, fed by the
-- per-link obligation `perLink` (now PROVED in `PerLink.Exp`).
--
-- Milestone 2b closes the general (arbitrary non-empty `Unique` config)
-- case: `perLink` is imported from `PerLink.Exp` and the four headline
-- theorems are stated modulo ONLY the module-level certified König/classical
-- axioms (Par-Diverges→, DRImpliesFD), as elsewhere in the FD layer.  The
-- ALL-SINGLETON results are now COROLLARIES of the general path (their
-- singleton hypothesis manufactures the `≢ []` + `Unique` obligations).
--
-- audit note: prose below says "axiom" rather than the p-word, so that a
-- grep -cw audit for the p-word counts only real declarations (now 0 in
-- this module).
------------------------------------------------------------------------

open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; trans; subst)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.AllPairs as AP
import Data.List.Relation.Unary.All as All
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.NetworkVerification.NetworkLinkEquiv
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open import CSP.Examples.Cardano_network.Net p
  using (Net; Net-≟; Link)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs)
open Params p using (linkConfig)

-- the generic `OffersOnly`/`≈DR`-congruence layer, instantiated at `E = Net Data`
open import CSP.Laws.Bisim.DRCongruenceRep (Net-≟ {Data})
  using (cong-⦀Fin)

open import Semantics.DRBisim {E = Net Data} {I = ExtI (Net Data)}
  using (_≈DR_)
open import Semantics.FailuresDivergences {E = Net Data} {I = ExtI (Net Data)}
  using (_⊑FD_; _≈FD_)
open import Semantics.DRImpliesFD {E = Net Data} {I = ExtI (Net Data)}
  using (drbisim→≈FD)

open import CSP.Examples.Cardano_network.Network p Data
  using (CopySpec; linkCopy)
open import CSP.Examples.Cardano_network.NetworkLink p Data
  using (NetworkLink; NetOneLink)
open import CSP.Examples.Cardano_network.NetworkVerification.NetworkLinkOffers p Data
  using (linkAlpha; linkAlpha-disj; oo-NetOneLink; oo-linkCopy)
-- the GENERAL per-link result, PROVED without any axiom (Milestone 2b capstone):
-- `perLink : (l : Link) → linkConfig l ≢ [] → Unique (linkConfig l)
--          → NetOneLink l ≈DR linkCopy l`
open import CSP.Examples.Cardano_network.NetworkVerification.PerLink.Exp p Data
  using (perLink)

------------------------------------------------------------------------
-- MILESTONE-2b COMPLETION.  The single-link mux-vs-copies equivalence —
-- the last remaining obligation of the GENERAL (multi-cell / arbitrary-
-- config) case — is now PROVED in `PerLink.Exp` (imported above) and this
-- module no longer declares any axiom.  The design is recorded in
-- docs/superpowers/specs/2026-07-12-perlink-milestone-2b-design.md; the
-- proof runs a genuine `⦀⋆`-fold of Copy cells against the multi-instance
-- mux (Layers `Leaf` → `Fold` → `Exp`).  `perLink` carries the two HONEST
-- hypotheses uncovered by the Phase-2 spike:
--   · `linkConfig l ≢ []`  — the empty-config SOUNDNESS finding: at the
--     empty config `linkCopy l = ⦀⋆ [] = Skip`, which terminates (√s),
--     whereas `NetOneLink l` (a never-terminating mux loop) never √s, so
--     the two are NOT DR-bisimilar there; the non-empty hypothesis rules
--     that degenerate cell out.
--   · `Unique (linkConfig l)` — needed for the `⦀⋆` fold step-elimination
--     (the per-cell `input` refutation goes through instance-disjointness).
-- OPEN NOTE (whether `Unique` is semantically necessary): now PARTIALLY
-- answered.  The Fold decode task showed `Unique` is genuinely needed at
-- the DECODE level — a duplicate cell turns a solo fire into an `evBoth`
-- overlap (two cells offering the same event), which the single-cell fold
-- step-elimination cannot classify; whether some coarser decode could
-- tolerate duplicates remains open.
-- The four headline theorems below drop the `Data →` witness the former
-- axiom used to carry: `perLink` exhibits every step by construction, so no
-- payload inhabitant is needed.
------------------------------------------------------------------------

-- master key: the link-indexed network is DR-bisimilar to the copy spec
-- (general case, threading the per-link Configured + Unique hypotheses)
netLink≈DR : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
           → NetworkLink ≈DR CopySpec
netLink≈DR hyp =
  cong-⦀Fin linkAlpha
    (λ i j i≢j → linkAlpha-disj i≢j)
    oo-NetOneLink oo-linkCopy
    (λ l → perLink l (proj₁ (hyp l)) (proj₂ (hyp l)))

-- headline: failures-divergences equivalence (FDR's [FD= both ways)
netLink≈FD : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
           → NetworkLink ≈FD CopySpec
netLink≈FD hyp = drbisim→≈FD (netLink≈DR hyp)

-- the two refinement directions separately
netLink⊑FD : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
           → NetworkLink ⊑FD CopySpec
netLink⊑FD hyp = proj₁ (netLink≈FD hyp)

spec⊑FD-Link : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l))
             → CopySpec ⊑FD NetworkLink
spec⊑FD-Link hyp = proj₂ (netLink≈FD hyp)

------------------------------------------------------------------------
-- ALL-SINGLETON COROLLARIES.  Every link configured with a single
-- instance is a special case of the general theorem: a singleton config
-- `c ∷ []` is manifestly non-empty and trivially `Unique`, so the general
-- `perLink` / `netLink≈DR` apply directly.  (Milestone 2a shipped these
-- via a bespoke singleton expansion `PerLink.Exp.perLink-single`, now
-- SUBSUMED by the general proof and deleted.)
------------------------------------------------------------------------

-- a singleton list is `Unique` (its `AllPairs` witness is `All.[] ∷ AP.[]`)
uniqSingleton : (c : Dir × IDs) → Unique (c ∷ [])
uniqSingleton c = AP._∷_ All.[] AP.[]

-- per-link singleton corollary: derive `≢ []` + `Unique` from the config
-- equation and route through the GENERAL `perLink`
perLink-single : (l : Link)(dc : Dir)(idc : IDs)
               → linkConfig l ≡ (dc , idc) ∷ []
               → NetOneLink l ≈DR linkCopy l
perLink-single l dc idc cfg≡ =
  perLink l ne (subst Unique (sym cfg≡) (uniqSingleton (dc , idc)))
  where
  -- non-empty: an empty config would equate `(dc , idc) ∷ []` with `[]`
  ne : linkConfig l ≢ []
  ne eq with trans (sym cfg≡) eq
  ... | ()

-- master key at all-singleton configs: DR-bisimilar to the copy spec
-- — modulo the module-level certified König/classical axioms
-- (Par-Diverges→, DRImpliesFD), as elsewhere in the FD layer
netLink≈DR-single : (∀ l → Σ[ c ∈ Dir × IDs ] linkConfig l ≡ c ∷ [])
                  → NetworkLink ≈DR CopySpec
netLink≈DR-single sing = netLink≈DR hyp
  where
  -- build the general hypothesis (`≢ []` × `Unique`) from each singleton witness
  hyp : ∀ l → linkConfig l ≢ [] × Unique (linkConfig l)
  hyp l with sing l
  ... | c , cfg≡ = ne , subst Unique (sym cfg≡) (uniqSingleton c)
    where
    ne : linkConfig l ≢ []
    ne eq with trans (sym cfg≡) eq
    ... | ()

-- headline: failures-divergences equivalence at all-singleton configs
-- — modulo the module-level certified König/classical axioms
-- (Par-Diverges→, DRImpliesFD), as elsewhere in the FD layer
netLink≈FD-single : (∀ l → Σ[ c ∈ Dir × IDs ] linkConfig l ≡ c ∷ [])
                  → NetworkLink ≈FD CopySpec
netLink≈FD-single sing = drbisim→≈FD (netLink≈DR-single sing)

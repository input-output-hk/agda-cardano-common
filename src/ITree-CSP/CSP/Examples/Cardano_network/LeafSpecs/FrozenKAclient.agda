{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- DEMO INSTANTIATION of `CSP.Laws.FD.FrozenComponent` on a REAL peer:
-- the KeepAlive CLIENT, which is one of the three genuinely frozen
-- undriven peers of the four-node diamond (the others being the
-- LeiosNotify and LeiosFetch clients).
--
--     (Stop ⦀ Rest) ∥⇘ A ⇙ D  ⊑F  (KAclientA l d ⦀ Rest) ∥⇘ A ⇙ D
--
-- generic in the link `l`, the direction `d`, the sibling bundle `Rest`
-- and the driver `D` — so ONE proof covers every instance of this peer
-- kind.  The peer-specific content is exactly the two `Frozen` fields:
--
--   * `KAclient-stable`  — the client's initial node has no enabled τ
--     (`pchoice` under `iter` under `renameMap` keeps the τ-map empty);
--   * `KAclient-confine` — every visible event it offers is on the
--     `apiKA` channel (four `KAEv` constructors, three refuted by the
--     menu returning `nothing`, the fourth landing in `Δ` outright).
--
-- The `Δ ⊆ A` containment and the `Partner Δ A D` driver invariant are
-- taken as parameters: the first is a per-alphabet one-liner-per-channel
-- fact about `apiES`, the second is a PER-NODE obligation (one witness
-- per driver bundle, shared by all frozen peers of that node), so
-- neither belongs to the per-peer instantiation cost.
--
-- No postulates (beyond `ParallelRefusals.offer-LEM`, inherited), no
-- holes, no pragmas.  Nothing from `NetworkVerification/*` is imported
-- and no composite is ever forced.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.LeafSpecs.FrozenKAclient (p : Params) where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open PTree

open Params p

open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p using (Payload; DecEq-Payload)
open import CSP.Examples.Cardano_network.Net p
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( KAclientA; ιKA; ιKA⁻¹; ιKA-linv )
open import CSP.Examples.Cardano_network.KeepAlive p
  using ( KAEv; KAEv-≟; sendKA; receiveKA; apiKAev; doneKA
        ; KAState; stClient; clientStep )
-- the two generic inversion lemmas of the calibrated leaf precedent are reused
-- verbatim; nothing else of that module is needed here
open import CSP.Examples.Cardano_network.LeafSpecs.KAclient p
  using ( ren-ev-inv; ιKA⁻¹-inv; nj )

import CSP.Operators {E = KAEv} KAEv-≟ as SrcOp
import CSP.Rename {E₁ = KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op

open import Semantics.LTS       {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
open import Semantics.Refusals  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Offers )
open import Semantics.Failures  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _⊑F_ )
open import Semantics.Stability {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( react-no-τ→stable )

open import CSP.Laws.FD.FrozenComponent {E = Net_Api Payload} (Net_Api-≟ {Payload})
  using ( Frozen; stableT; confine; Partner; frozen-delete-⊑F )

-- process trees over the shared alphabet (as in the leaf precedent)
NetTree : Set₁
NetTree = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

------------------------------------------------------------------------
-- Section 1 — the confinement alphabet Δ
------------------------------------------------------------------------

-- `Δ`: the whole `apiKA` channel.  Every visible event the KeepAlive client can offer
-- is on it, and no driver of the four-node diamond ever offers an `apiKA` event.  It is
-- deliberately NOT refined by `(l , d)`: the drivers avoid the channel wholesale, and
-- the coarser predicate makes `confine` a single clause covering all four api tags.
ΔKA : (at : AnyTypes (Net_Api Payload)) → proj₁ at → Set
ΔKA (_ , apiKA _ _ _) _ = ⊤₀
ΔKA _                 _ = ⊥

------------------------------------------------------------------------
-- Section 2 — the two `Frozen` fields (the whole per-peer cost)
------------------------------------------------------------------------

-- the client's initial node has no enabled τ: `clientStep l d stClient` is a `pchoice`
-- (empty τ-map), `iter-bind` transports the empty τ-map through `iterT`, and `renameMap`
-- transports it through `extBranch`, so every τ-branch is `nothing`
KAclient-stable : (l : Link) (d : Dir) → isStable (KAclientA l d)
KAclient-stable l d = react-no-τ→stable {t = KAclientA l d} refl noτ
  where
    noτ : ∀ {t′ : NetTree} → KAclientA l d ─[ τ ]─► t′ → ⊥
    noτ (sSil ())
    noτ (sTau {i = A , eι₂} {a = a} refl br) with RenKA.extBwd eι₂ | br
    ... | nothing  | ()
    ... | just eι₁ | ()

-- every visible event the client offers is on the `apiKA` channel: invert the renaming
-- (`ren-ev-inv`) to a source `KAEv`, and read off `clientStep l d stClient`'s menu —
-- `sendKA`/`receiveKA`/`doneKA` are `nothing` there, and an `apiKAev` maps to `apiKA`
KAclient-confine : (l : Link) (d : Dir) {X : Set} {f : Net_Api Payload X} {a : X}
                 → Offers (KAclientA l d) (evl (evLabel X f a)) → ΔKA (X , f) a
KAclient-confine l d (_ , stp)
  with ren-ev-inv (SrcOp.iter (clientStep l d) stClient) refl stp
... | sendKA _ _      , _ , _   , eqv , _ = ⊥-elim (nj eqv)
... | receiveKA _ _   , _ , _   , eqv , _ = ⊥-elim (nj eqv)
... | doneKA _ _      , _ , _   , eqv , _ = ⊥-elim (nj eqv)
... | apiKAev _ _ _   , _ , eqι , _   , _ rewrite ιKA⁻¹-inv eqι = tt₀

-- the bundled hypothesis
KAclient-Frozen : (l : Link) (d : Dir) → Frozen ΔKA (KAclientA l d)
KAclient-Frozen l d .stableT = KAclient-stable l d
KAclient-Frozen l d .confine = KAclient-confine l d

------------------------------------------------------------------------
-- Section 3 — the instantiated deletion law
------------------------------------------------------------------------

-- THE INSTANCE.  For every synchronisation set `A` containing the `apiKA` channel
-- (`apiES` does: `apiSet (_ , apiKA _ _ _) = ⊤`), every link, direction, sibling bundle
-- and `apiKA`-avoiding driver, the KeepAlive client may be deleted in favour of `Stop`
-- as a stable-failures refinement.  Lifting this through the surrounding `⦀` of bundles,
-- the `⦀` of nodes, the outer `∥⇘ ioES ⇙` and the two hides is then pure
-- `⦀-mono-⊑F` / `Par-mono-⊑F` / `Hide-mono-⊑F`.
KAclient-delete-⊑F :
    (A : Op.EventSet)
  → (∀ {X : Set} {f : Net_Api Payload X} {a : X}
       → ΔKA (X , f) a → Op.EventSet.mem A (X , f) a)
  → (l : Link) (d : Dir) (Rest D : NetTree) → Partner ΔKA A D
  → ((Op.Stop Op.⦀ Rest) Op.∥⇘ A ⇙ D) ⊑F ((KAclientA l d Op.⦀ Rest) Op.∥⇘ A ⇙ D)
KAclient-delete-⊑F A Δ⊆A l d Rest D pd =
  frozen-delete-⊑F A ΔKA Δ⊆A (KAclientA l d) Rest D (KAclient-Frozen l d) pd

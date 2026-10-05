{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- FourNode liveness M3 — DIRECTION-GENERALIZED spec/driver confinement
-- for the PRODUCE-side nodes (A, and the produce leg of B/C).
--
-- nodeA/B/C are lo-endpoints on their produce links, so they compose
-- `miniProtocols l lo hi` (client dir lo, server dir hi) — the MIRROR of
-- M1/M2's `miniProtocols l hi lo`.  All the SPEC peers (`kaClientSpec`,
-- …) and their link-confinement lemmas (`…-onLink`, in `NodeDOffers`)
-- are already ∀ d, so the flipped spec bundle `specBundleFlip` and its
-- confinement `specBundleFlip-onLink` come for free here (dir hi↔lo
-- swapped throughout).  The produce driver's tight apiES confinement
-- (`produce-OO-api`, the produce analogue of M1's `consume-OO-api`) is
-- also proved here.
--
-- What is NOT here (and is the remaining M3 obligation): the flipped
-- BUNDLE bisim `miniProtocols l lo hi ≈DR specBundleFlip l`.  The eight
-- per-peer ≈DR proofs bake their dir literal (`Tks l = … kaSnxt l lo`,
-- relation ctors carry `l lo`/`l hi`), so they must be re-established at
-- the flipped dir (server at hi, client at lo) — a mechanical dir-swap
-- copy of the M1 peer-bisim modules, cf. the M3 report handoff.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; produce; consume; apiES; Block₃; b1; linkAB; linkAC )
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net p
open import CSP.Examples.Cardano_network.NetworkPar p using ( miniProtocols )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _⦀_; _>>=_; _>>_; Skip )

open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; Disj; OffersOnly; OffersOnly-⦀
        ; OffersOnly-Prefix; OffersOnly-Prefix₀; OffersOnly-Output
        ; OffersOnly-Ret; OffersOnly-Skip; OffersOnly->>= )

-- the M1 contract surface (NetTree + all τ-free spec peers)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePair
-- the value-blind api alphabet (`apiAlpha at a = apiES.mem at a`)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairAssembly
  using ( apiAlpha )
-- the ∀ d spec-peer link-confinement lemmas (reused at the flipped dirs)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeDOffers
  using ( apiLinkAlpha; apiLinkAlpha-disj
        ; kaClientSpec-onLink; kaServerSpec-onLink
        ; csClientSpec-onLink; csServerSpec-onLink
        ; bfClientSpec-onLink; bfServerSpec-onLink
        ; tsClientSpec-onLink; tsServerSpec-onLink )

module CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeAOffers where

-- nodeA's two produce links are distinct (linkAB = #0, linkAC = #1); gives the
-- inner `cong-⦀` its `Sep ∅ES` via `apiLinkAlpha-disj linkAB≢linkAC`
linkAB≢linkAC : ¬ linkAB ≡ linkAC
linkAB≢linkAC ()

------------------------------------------------------------------------
-- PRODUCE-side driver confinement (the produce analogue of `consume-OO-api`).
------------------------------------------------------------------------

-- the produce driver confines TIGHTLY to apiES (only apiCS/apiBF fire; all ∈ apiES)
produce-OO-api : (l : Link) (d : Dir) (blk : Block₃)
               → OffersOnly apiAlpha (produce l d blk)
produce-OO-api l d blk =
  OffersOnly-Prefix₀ (λ _ → tt)
    (OffersOnly-Prefix₀ (λ _ → tt)
      (OffersOnly-Output tt
        (OffersOnly-Prefix (λ _ → tt)
          (λ _ →
            OffersOnly-Output tt
              (OffersOnly-Output tt
                (OffersOnly-Output tt OffersOnly-Skip))))))

-- the consume BODY confines to apiES (= the left leg of M1's `consume-OO-api`,
-- exposed without the trailing `>> Skip` so the bind-coupled relay can reuse it)
consume-body-OO : (l : Link) → OffersOnly apiAlpha (consume l hi)
consume-body-OO l =
  OffersOnly-Prefix₀ (λ _ → tt)
    (OffersOnly-Prefix (λ _ → tt)
      (λ { (header b , _) →
        OffersOnly-Output tt
          (OffersOnly-Prefix (λ _ → tt)
            (λ b′ →
              OffersOnly-Output tt
                (OffersOnly-Prefix₀ (λ _ → tt) OffersOnly-Ret)))}))

-- the bind-coupled RELAY driver of nodeB/nodeC confines to apiES:
-- `consume l hi >>= λ b → produce l′ hi b`
relay-OO-api : (l l′ : Link)
             → OffersOnly apiAlpha (consume l hi >>= λ b → produce l′ hi b)
relay-OO-api l l′ =
  OffersOnly->>= (consume-body-OO l) (λ b → produce-OO-api l′ hi b)

------------------------------------------------------------------------
-- The flipped spec bundle (mirror of `miniProtocols l lo hi`) + confinement.
------------------------------------------------------------------------

-- the τ-free spec bundle for the PRODUCE orientation (client lo, server hi)
specBundleFlip : (l : Link) → NetTree
specBundleFlip l =
  kaClientSpec l lo ⦀ (kaServerSpec l hi
    ⦀ (csClientSpec l lo ⦀ (csServerSpec l hi
    ⦀ (bfClientSpec l lo ⦀ (bfServerSpec l hi
    ⦀ (tsClientSpec l lo ⦀ tsServerSpec l hi))))))

-- the flipped spec bundle offers only link-`l` events (8-fold OffersOnly-⦀)
specBundleFlip-onLink : (l : Link) → OffersOnly (apiLinkAlpha l) (specBundleFlip l)
specBundleFlip-onLink l =
  OffersOnly-⦀ (kaClientSpec-onLink l lo)
    (OffersOnly-⦀ (kaServerSpec-onLink l hi)
    (OffersOnly-⦀ (csClientSpec-onLink l lo)
    (OffersOnly-⦀ (csServerSpec-onLink l hi)
    (OffersOnly-⦀ (bfClientSpec-onLink l lo)
    (OffersOnly-⦀ (bfServerSpec-onLink l hi)
    (OffersOnly-⦀ (tsClientSpec-onLink l lo) (tsServerSpec-onLink l hi)))))))

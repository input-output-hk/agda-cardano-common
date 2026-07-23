{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- FourNode liveness campaign — M3: `nodeA ≈DR nodeASpec`
-- (`Liveness.NodeA`).  The produce-side node A is the two AB/AC link
-- bundles interleaved (client on lo, server on hi — the FLIP of node D),
-- synchronised on `apiES` with the two produce drivers interleaved:
--
--   nodeA = (miniProtocols linkAB lo hi ⦀ miniProtocols linkAC lo hi)
--             ∥⇘ apiES ⇙ (produce linkAB hi b1 ⦀ produce linkAC hi b1)
--
-- `nodeASpec` MIRRORS that shape verbatim, replacing each mini-protocol
-- bundle by its FLIPPED τ-free spec bundle (`specBundleFlip`) and keeping
-- the two produce drivers UNCHANGED:
--
--   nodeASpec = (specBundleFlip linkAB ⦀ specBundleFlip linkAC)
--             ∥⇘ apiES ⇙ (produce linkAB hi b1 ⦀ produce linkAC hi b1)
--
-- The proof is the exact MIRROR of `NodeD.nodeD≈DR`: a pure congruence
-- over nodeA's skeleton — outer `cong-Par⊤ apiES` (driver pair verbatim →
-- `drbisim-refl`; the three `Sep apiES` from `sep-R drvPairA-OO`, the
-- produce pair offering only apiES events), inner `cong-⦀` of the two
-- FLIPPED bundle bisims `b0flip linkAB`/`b0flip linkAC` (whose three
-- `Sep ∅ES` hold via the disjoint link alphabets `apiLinkAlpha`).  The
-- impl-side link confinement `implBundleFlip-onLink` is derived for free
-- via `≈DR-OO` from `b0flip` + the flipped spec-bundle confinement.
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Process_Trees
open PTree

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; produce; apiES; b1; linkAB; linkAC; nodeA )
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net p

open import CSP.Examples.Cardano_network.NetworkPar p
  using ( miniProtocols )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; ∅ES; EventSet )
open EventSet using ( mem )

open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _≈DR_; drbisim-refl )
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}

open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload})
  using ( Sep; cong-⦀; cong-Par⊤ )
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; Disj; OffersOnly; OffersOnly-⦀; OffersOnly-mono
        ; sep-from-OffersOnly; ≈DR-OO )

-- the M1 contract surface (NetTree)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePair
  using ( NetTree )
-- the driver-Sep helper `sep-R` + value-blind api alphabet `apiAlpha`
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairAssembly
  using ( sep-R; apiAlpha )
-- the link-refined alphabet + its BD/CD-style disjointness
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeDOffers
  using ( apiLinkAlpha; apiLinkAlpha-disj )
-- the flipped spec bundle + confinement + produce-driver OO + link ≢
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeAOffers
  using ( specBundleFlip; specBundleFlip-onLink; produce-OO-api; linkAB≢linkAC )
-- the flipped per-link bundle bisim `b0flip l : miniProtocols l lo hi ≈DR specBundleFlip l`
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairAssemblyFlip
  using ( b0flip )

module CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeA where

-- the abstract node A: the two FLIPPED spec bundles under nodeA's exact skeleton
nodeASpec : NetTree
nodeASpec =
  (specBundleFlip linkAB ⦀ specBundleFlip linkAC)
    ∥⇘ apiES ⇙ (produce linkAB hi b1 ⦀ produce linkAC hi b1)

-- the interleaved produce driver pair confines to apiES (seam gap (iii) via sep-R)
drvPairA-OO : OffersOnly apiAlpha (produce linkAB hi b1 ⦀ produce linkAC hi b1)
drvPairA-OO = OffersOnly-⦀ (produce-OO-api linkAB hi b1) (produce-OO-api linkAC hi b1)

-- impl-side link confinement, derived for free via ≈DR-OO from b0flip + spec conf.
implBundleFlip-onLink : (l : Link) → OffersOnly (apiLinkAlpha l) (miniProtocols l lo hi)
implBundleFlip-onLink l = ≈DR-OO (b0flip l) (specBundleFlip-onLink l)

-- the M3 milestone theorem (mirror of NodeD.nodeD≈DR at the flipped dirs)
nodeA≈DR : nodeA ≈DR nodeASpec
nodeA≈DR =
  cong-Par⊤ apiES
    (sep-R drvPairA-OO (λ x → x) _)
    (sep-R drvPairA-OO (λ x → x) _)
    (sep-R drvPairA-OO (λ x → x) _)
    (cong-⦀
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkAB≢linkAC at a) (implBundleFlip-onLink linkAB) (implBundleFlip-onLink linkAC))
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkAB≢linkAC at a) (specBundleFlip-onLink linkAB) (implBundleFlip-onLink linkAC))
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkAB≢linkAC at a) (specBundleFlip-onLink linkAB) (specBundleFlip-onLink linkAC))
      (b0flip linkAB) (b0flip linkAC))
    (drbisim-refl _)

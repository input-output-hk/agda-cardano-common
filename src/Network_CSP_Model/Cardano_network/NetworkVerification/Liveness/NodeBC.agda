{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- FourNode liveness campaign — M3 (part 3): `nodeB ≈DR nodeBSpec` and
-- `nodeC ≈DR nodeCSpec` (`Liveness.NodeBC`).  The RELAY nodes B and C are
-- each a MIXED-orientation pair of link bundles (one straight `hi lo`
-- leg, one flipped `lo hi` leg) interleaved, synchronised on `apiES`
-- with the bind-coupled relay driver `consume … >>= λ b → produce …`:
--
--   nodeB = (miniProtocols linkAB hi lo ⦀ miniProtocols linkBD lo hi)
--             ∥⇘ apiES ⇙ (consume linkAB hi >>= λ b → produce linkBD hi b)
--   nodeC = (miniProtocols linkAC hi lo ⦀ miniProtocols linkCD lo hi)
--             ∥⇘ apiES ⇙ (consume linkAC hi >>= λ b → produce linkCD hi b)
--
-- Each spec MIRRORS that shape verbatim: the STRAIGHT bundle becomes the
-- M1 `specBundle`, the FLIPPED bundle becomes the M3 `specBundleFlip`,
-- and the relay driver is kept UNCHANGED:
--
--   nodeBSpec = (specBundle linkAB ⦀ specBundleFlip linkBD)
--             ∥⇘ apiES ⇙ (consume linkAB hi >>= λ b → produce linkBD hi b)
--   nodeCSpec = (specBundle linkAC ⦀ specBundleFlip linkCD)
--             ∥⇘ apiES ⇙ (consume linkAC hi >>= λ b → produce linkCD hi b)
--
-- The proof is the exact MIRROR of `NodeD.nodeD≈DR` / `NodeA.nodeA≈DR`:
-- a pure congruence over the node skeleton — outer `cong-Par⊤ apiES`
-- (relay driver verbatim → `drbisim-refl`; the three `Sep apiES` from
-- `sep-R (relay-OO-api …)`, the bind-coupled relay offering only apiES
-- events), inner `cong-⦀` mixing ONE straight bundle bisim `b0`
-- (→ `specBundle`) with ONE flipped bundle bisim `b0flip`
-- (→ `specBundleFlip`), whose three `Sep ∅ES` hold via the disjoint link
-- alphabets `apiLinkAlpha` (linkAB≢linkBD / linkAC≢linkCD).  The flipped
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
  using ( p; consume; produce; apiES; linkAB; linkAC; linkBD; linkCD; nodeB; nodeC )
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net p

open import CSP.Examples.Cardano_network.NetworkPar p
  using ( miniProtocols )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _>>=_; ∅ES; EventSet )
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
-- the M1 straight bundle bisim `b0 l : miniProtocols l hi lo ≈DR specBundle l`
-- + the driver-Sep helper `sep-R` + value-blind api alphabet `apiAlpha`
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairAssembly
  using ( b0; sep-R; apiAlpha )
-- the link-refined alphabet + its disjointness + straight bundle confinement
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeDOffers
  using ( apiLinkAlpha; apiLinkAlpha-disj; specBundle; specBundle-onLink; implBundle-onLink )
-- the flipped spec bundle + confinement + bind-coupled relay-driver OO
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeAOffers
  using ( specBundleFlip; specBundleFlip-onLink; relay-OO-api )
-- the flipped per-link bundle bisim `b0flip l : miniProtocols l lo hi ≈DR specBundleFlip l`
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairAssemblyFlip
  using ( b0flip )

module CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeBC where

------------------------------------------------------------------------
-- Link-distinctness lemmas for the inner `cong-⦀` `Sep ∅ES` (trivial
-- `()` on distinct `Fin 4` literals: linkAB=#0, linkBD=#2, linkAC=#1,
-- linkCD=#3).
------------------------------------------------------------------------

-- nodeB's two links AB (#0) and BD (#2) are distinct
linkAB≢linkBD : ¬ linkAB ≡ linkBD
linkAB≢linkBD ()

-- nodeC's two links AC (#1) and CD (#3) are distinct
linkAC≢linkCD : ¬ linkAC ≡ linkCD
linkAC≢linkCD ()

------------------------------------------------------------------------
-- The flipped impl-side link confinement, derived for free via `≈DR-OO`
-- from `b0flip` + the flipped spec-bundle confinement (mirror of NodeA).
------------------------------------------------------------------------

-- flipped impl bundle offers only link-`l` events (transported from spec)
implBundleFlip-onLink : (l : Link) → OffersOnly (apiLinkAlpha l) (miniProtocols l lo hi)
implBundleFlip-onLink l = ≈DR-OO (b0flip l) (specBundleFlip-onLink l)

------------------------------------------------------------------------
-- Node B: `nodeB ≈DR nodeBSpec`.
------------------------------------------------------------------------

-- the abstract node B: straight AB spec bundle ⦀ flipped BD spec bundle
nodeBSpec : NetTree
nodeBSpec =
  (specBundle linkAB ⦀ specBundleFlip linkBD)
    ∥⇘ apiES ⇙ (consume linkAB hi >>= λ b → produce linkBD hi b)

-- the bind-coupled relay driver confines to apiES (seam gap (iii) via sep-R)
drvB-OO : OffersOnly apiAlpha (consume linkAB hi >>= λ b → produce linkBD hi b)
drvB-OO = relay-OO-api linkAB linkBD

-- the M3 milestone theorem for node B (mirror of NodeD.nodeD≈DR, mixed legs)
nodeB≈DR : nodeB ≈DR nodeBSpec
nodeB≈DR =
  cong-Par⊤ apiES
    (sep-R drvB-OO (λ x → x) _)
    (sep-R drvB-OO (λ x → x) _)
    (sep-R drvB-OO (λ x → x) _)
    (cong-⦀
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkAB≢linkBD at a) (implBundle-onLink linkAB) (implBundleFlip-onLink linkBD))
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkAB≢linkBD at a) (specBundle-onLink linkAB) (implBundleFlip-onLink linkBD))
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkAB≢linkBD at a) (specBundle-onLink linkAB) (specBundleFlip-onLink linkBD))
      (b0 linkAB) (b0flip linkBD))
    (drbisim-refl _)

------------------------------------------------------------------------
-- Node C: `nodeC ≈DR nodeCSpec` (AC/CD analogue of node B).
------------------------------------------------------------------------

-- the abstract node C: straight AC spec bundle ⦀ flipped CD spec bundle
nodeCSpec : NetTree
nodeCSpec =
  (specBundle linkAC ⦀ specBundleFlip linkCD)
    ∥⇘ apiES ⇙ (consume linkAC hi >>= λ b → produce linkCD hi b)

-- the bind-coupled relay driver confines to apiES (seam gap (iii) via sep-R)
drvC-OO : OffersOnly apiAlpha (consume linkAC hi >>= λ b → produce linkCD hi b)
drvC-OO = relay-OO-api linkAC linkCD

-- the M3 milestone theorem for node C (mirror of nodeB≈DR at AC/CD)
nodeC≈DR : nodeC ≈DR nodeCSpec
nodeC≈DR =
  cong-Par⊤ apiES
    (sep-R drvC-OO (λ x → x) _)
    (sep-R drvC-OO (λ x → x) _)
    (sep-R drvC-OO (λ x → x) _)
    (cong-⦀
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkAC≢linkCD at a) (implBundle-onLink linkAC) (implBundleFlip-onLink linkCD))
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkAC≢linkCD at a) (specBundle-onLink linkAC) (implBundleFlip-onLink linkCD))
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkAC≢linkCD at a) (specBundle-onLink linkAC) (specBundleFlip-onLink linkCD))
      (b0 linkAC) (b0flip linkCD))
    (drbisim-refl _)

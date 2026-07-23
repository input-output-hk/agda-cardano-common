{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- FourNode liveness campaign — M2: `nodeD ≈DR nodeDSpec`
-- (`Liveness.NodeD`).  The consume-side node D is the two BD/CD link
-- bundles interleaved, synchronised on `apiES` with the two consume
-- drivers interleaved:
--
--   nodeD = (miniProtocols linkBD hi lo ⦀ miniProtocols linkCD hi lo)
--             ∥⇘ apiES ⇙ ((consume linkBD hi >> Skip) ⦀ (consume linkCD hi >> Skip))
--
-- `nodeDSpec` MIRRORS that shape verbatim, replacing each mini-protocol
-- bundle by its τ-free spec bundle (the M1 `pipeSpec` left operand) and
-- keeping the two drivers UNCHANGED:
--
--   nodeDSpec = (specBundle linkBD ⦀ specBundle linkCD)
--             ∥⇘ apiES ⇙ ((consume linkBD hi >> Skip) ⦀ (consume linkCD hi >> Skip))
--
-- ============================ SEAM-CLOSURE ============================
-- The M1 review flagged three sub-gaps for M2 (nodeD is NOT syntactically
-- `pipe_BD ⦀ pipe_CD`).  The `nodeDSpec` SHAPE decision closes two of them
-- outright:
--
--  (i)  Par⊤/⦀ INTERCHANGE law — NOT NEEDED.  Mirroring nodeD's shape
--       (spec bundles under the SAME `⦀`/`∥⇘apiES⇙` skeleton) means
--       `nodeD ≈DR nodeDSpec` is a pure CONGRUENCE step: `cong-Par⊤ apiES`
--       over (left) `cong-⦀ (b0 linkBD) (b0 linkCD)` — the two M1 bundle
--       bisims — and (right) `drbisim-refl` for the verbatim driver pair.
--       No regrouping of nodeD into `pipe_BD ⦀ pipe_CD` is required, so the
--       interchange law that shape would have needed is avoided entirely.
--  (iii) OffersOnly-through-`∥⇘⇙` for a whole pipe — NOT NEEDED.  The
--       top-level `cong-Par⊤ apiES` `Sep`s are discharged by `sep-R`
--       (the driver pair offers ONLY apiES events, so it separates from
--       ANY left operand), exactly as in the M1 `pipe≈DR` assembly.
--  (ii) link-REFINED `Alpha` — the ONE genuinely new obligation.  The
--       inner `cong-⦀ (b0 linkBD) (b0 linkCD)` needs `Sep ∅ES` between the
--       BD and CD operands (impl·impl, spec·impl, spec·spec).  The M1
--       `peerAlpha` is link-BLIND (keys events to (protocol,dir) only), so
--       it does NOT separate same-(protocol,dir) peers on different links.
--       `apiLinkAlpha l` (below) refines by the event's LINK field; the
--       two bundles then confine to `apiLinkAlpha linkBD` / `apiLinkAlpha
--       linkCD`, disjoint since `linkBD ≢ linkCD`.
--
-- SHAPE reasoning (recorded): the mirror shape is cleanest for BOTH M2 and
-- M5.  For M2 it removes the interchange law and gap (iii) (see above).
-- For M4/M5 it keeps `nodeDSpec` STRUCTURALLY PARALLEL to `nodeD` (same
-- `⦀`/`∥⇘apiES⇙` skeleton, drivers verbatim), so M4's congruence
-- substitution of node specs and M5's abstract-system walk face a spec
-- whose operator tree matches the impl's, with only the τ-free table FSMs
-- swapped in — no re-bracketing to reconcile.
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
  using ( p; consume; apiES; linkBD; linkCD; nodeD )
open import CSP.Examples.Cardano_network.Params using (Params)
open Params p
open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Net p

open import CSP.Examples.Cardano_network.NetworkPar p
  using ( KAclientA; KAserverA; CSclientA; CSserverA
        ; BFclientA; BFserverA; TSclientA; TSserverA; miniProtocols )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _>>_; Skip; ∅ES; EventSet )
open EventSet using ( mem )

open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _≈DR_; drbisim-refl )
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}

open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload})
  using ( Sep; cong-⦀; cong-Par⊤ )
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; Disj; OffersOnly; OffersOnly-⦀; OffersOnly-mono; sep-from-OffersOnly )

-- the M1 contract surface (NetTree)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePair
  using ( NetTree )
-- the M1 per-link bundle bisim `b0 l : miniProtocols l hi lo ≈DR specBundle l`
-- + driver-side confinement helpers (reused verbatim)
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePairAssembly
  using ( b0; sep-R; apiAlpha; consume-OO-api )
-- seam gap (ii): the link-refined alphabet + spec/impl bundle confinement
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeDOffers
  using ( apiLinkAlpha; apiLinkAlpha-disj; linkBD≢linkCD
        ; specBundle; implBundle-onLink; specBundle-onLink )

module CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeD where

------------------------------------------------------------------------
-- The abstract node D's spec (`specBundle` reused from NodeDOffers).
------------------------------------------------------------------------

-- the abstract node D: the two spec bundles under nodeD's exact skeleton
nodeDSpec : NetTree
nodeDSpec =
  (specBundle linkBD ⦀ specBundle linkCD)
    ∥⇘ apiES ⇙ ((consume linkBD hi >> Skip {0ℓ}) ⦀ (consume linkCD hi >> Skip {0ℓ}))

------------------------------------------------------------------------
-- TOP-LEVEL driver-pair confinement (seam gap (iii) discharged by `sep-R`).
-- The two consume drivers each offer only apiES events, so their `⦀`
-- offers only apiES events; `sep-R` then separates it from ANY left
-- operand under the `apiES` sync set.
------------------------------------------------------------------------

-- the interleaved driver pair confines to apiES
drvPair-OO : OffersOnly apiAlpha
  ((consume linkBD hi >> Skip {0ℓ}) ⦀ (consume linkCD hi >> Skip {0ℓ}))
drvPair-OO = OffersOnly-⦀ (consume-OO-api linkBD) (consume-OO-api linkCD)

------------------------------------------------------------------------
-- M2 MILESTONE: nodeD ≈DR nodeDSpec.
--
-- Pure congruence over nodeD's skeleton (nodeD is NEVER stepped):
--   • outer `cong-Par⊤ apiES` — the driver pair is verbatim, so its leg is
--     `drbisim-refl`; the three `Sep apiES` side-conditions hold because the
--     driver pair offers ONLY apiES events (`sep-R drvPair-OO`);
--   • inner `cong-⦀` of the two M1 bundle bisims `b0 linkBD`/`b0 linkCD`,
--     whose three `Sep ∅ES` side-conditions hold because the BD/CD bundles
--     confine to the DISJOINT link alphabets `apiLinkAlpha linkBD/linkCD`.
------------------------------------------------------------------------

-- the M2 milestone theorem (inline-λ disjointness, per M1's assembly idiom)
nodeD≈DR : nodeD ≈DR nodeDSpec
nodeD≈DR =
  cong-Par⊤ apiES
    (sep-R drvPair-OO (λ x → x) _)
    (sep-R drvPair-OO (λ x → x) _)
    (sep-R drvPair-OO (λ x → x) _)
    (cong-⦀
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkBD≢linkCD at a) (implBundle-onLink linkBD) (implBundle-onLink linkCD))
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkBD≢linkCD at a) (specBundle-onLink linkBD) (implBundle-onLink linkCD))
      (sep-from-OffersOnly ∅ES (λ {at} {a} _ → apiLinkAlpha-disj linkBD≢linkCD at a) (specBundle-onLink linkBD) (specBundle-onLink linkCD))
      (b0 linkBD) (b0 linkCD))
    (drbisim-refl _)

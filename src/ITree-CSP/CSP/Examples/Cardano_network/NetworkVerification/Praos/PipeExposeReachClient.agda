{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the CLIENT visible-middle
-- (`Praos.PipeExposeReachClient`).
--
-- `PipeExposeNodeClient.liftτ*-clientReport` exposes the leg-`l` BF-CLIENT peers'
-- deltas across a hidden τ-run.  The strong VISIBLE api-CSBF middle of a weak
-- move needs the complementary fact: how those clients move across that visible
-- hop.  An api-CSBF event IS a NODE hand-off, so the nodes DO move on it; but
-- because `PipeExposeNode.adv-of : (q q′) → ClientAdv q q′` is TOTAL, the client
-- report reads DIRECTLY off the reflected successor `r′` that
-- `PipeExposeReach.reach-ev-both` already returns (no fresh cone) — exactly the
-- session-8 recipe adaptation, now applied to the visible middle.
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Nat using ( _<_ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeReachClient (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using ( EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( NetProc )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( RState; radec; rdec; toSys )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA
  using ( IsApiCSBF )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.Walk blkA
  using ( μTot )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeReach blkA
  using ( reach-ev-both )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeNodeClient blkA
  using ( AllClientAdv; allClientAdv-of; ClientReport; allClientAdv⇒ClientReport )

------------------------------------------------------------------------
-- The strong-visible api middle WITH the client report on the SAME `r′` (mirror
-- `PipeExposeReach.reach-ev-cell`, but for the BF-client peers).  Reuses
-- `reach-ev-both`'s reflected successor `r′` and reads `AllClientAdv` off it via
-- the total `allClientAdv-of` — no per-peer node cone.
------------------------------------------------------------------------

reach-ev-client : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × AllClientAdv (toSys r) (toSys r′)
reach-ev-client r aic apimem step with reach-ev-both r aic apimem step
... | r′ , Mr , wr , drop , _ , _ = r′ , Mr , wr , drop , allClientAdv-of (toSys r) (toSys r′)

------------------------------------------------------------------------
-- The leg-`l` projection of the visible-middle client frame (the plan's headline
-- for this piece): the two leg BF-client peers' `ClientAdv` across the api hop.
------------------------------------------------------------------------

reach-ev-clientReport : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′)
      × (rdec r ═[ ev (evl (evLabel X e a)) ]═► rdec r′)
      × (μTot (toSys r′) < μTot (toSys r)) × ClientReport l (toSys r) (toSys r′)
-- NB `let`-destructuring, NOT `with`: in this `(blkA : Block₃)`-parameterised
-- module a `with` abstracts the block out of the imported `PipeInv.upClient`
-- copy and the abstracted goal stops converting.
reach-ev-clientReport l r aic apimem step =
  let (r′ , Mr , wr , drop , acr) = reach-ev-client r aic apimem step
  in  r′ , Mr , wr , drop , allClientAdv⇒ClientReport l (toSys r) (toSys r′) acr

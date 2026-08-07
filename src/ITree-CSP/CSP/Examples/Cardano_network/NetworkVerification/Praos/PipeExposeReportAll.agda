{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the FULL seven-component `PipeReport⁺`
-- (`Praos.PipeExposeReportAll`).
--
-- `PipeExposeReport.liftReach-ev-both` already exposes the nodeD `DReport` and
-- the whole-medium `AllCellAdv` on ONE reflected successor `r′` across a weak
-- api-CSBF move.  This module folds in the remaining THREE node-side
-- components — the leg BF-client peers (`ClientReport`), the leg producer
-- driver (`ProdReport`), and the leg relay driver (`RelayReport`).
--
-- The merge is LIGHT: each of the three node reports is read off the endpoints
-- by a TOTAL classifier (`PipeExposeNodeClient.allClientAdv-of`,
-- `PipeExposeNodeProd.allProdAdv-of`, `PipeExposeNodeRelay.allRelayAdv-of`),
-- which returns a valid `AllXAdv (toSys r) (toSys r′)` for ANY endpoints.  So no
-- fresh reflection is needed — the three reports simply ride the SAME `r′` that
-- `liftReach-ev-both` already produced.  `liftReach-pipe⁺` bundles all five
-- report types (D + cell + client + prod + relay) into the leg-`l` `PipeReport⁺`.
--
-- No postulate/hole/meta.  All base modules stay READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeReportAll (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; apiES )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( NetProc; RState; radec; toSys )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( TwoLegs )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle blkA
  using ( IsApiCSBF )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkDExpose blkA
  using ( DReport )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeCell blkA
  using ( CellReport; allCellAdv⇒CellReport )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeNodeClient blkA
  using ( ClientReport; allClientAdv-of; allClientAdv⇒ClientReport )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeNodeProd blkA
  using ( ProdReport; allProdAdv-of; allProdAdv⇒ProdReport )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeNodeRelay blkA
  using ( RelayReport; allRelayAdv-of; allRelayAdv⇒RelayReport )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeReport blkA
  using ( liftReach-ev-both )

------------------------------------------------------------------------
-- The full seven-component leg-`l` report across a weak api-CSBF move: the
-- nodeD consumer `DReport`, the two leg medium cells `CellReport`, the two leg
-- BF-client peers `ClientReport`, the leg producer `ProdReport`, and the leg
-- relay `RelayReport`.
------------------------------------------------------------------------

PipeReport⁺ : TwoLegs → (s s′ : SysState) {X : Set 0ℓ} → Net_Api Payload X → X → Set₁
PipeReport⁺ l s s′ e a =
    DReport    s s′ e a
  × CellReport   l s s′
  × ClientReport l s s′
  × ProdReport   l s s′
  × RelayReport  l s s′

------------------------------------------------------------------------
-- HEADLINE: a weak api-CSBF move exposes ALL seven leg-`l` component deltas on
-- one reflected successor `r′`.  The D + cell halves come from
-- `liftReach-ev-both`; the client / prod / relay halves are read off the SAME
-- endpoints via their total classifiers (no fresh reflection).
------------------------------------------------------------------------

liftReach-pipe⁺ : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {t′ : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ═[ ev (evl (evLabel X e a)) ]═► t′
  → Σ[ r′ ∈ RState ] (t′ ≡ radec r′) × PipeReport⁺ l (toSys r) (toSys r′) e a
liftReach-pipe⁺ l r aic apimem w with liftReach-ev-both r aic apimem w
... | r′ , eq , drep , acr =
      r′ , eq ,
      ( drep
      , allCellAdv⇒CellReport     l (toSys r) (toSys r′) acr
      , allClientAdv⇒ClientReport l (toSys r) (toSys r′) (allClientAdv-of (toSys r) (toSys r′))
      , allProdAdv⇒ProdReport     l (toSys r) (toSys r′) (allProdAdv-of   (toSys r) (toSys r′))
      , allRelayAdv⇒RelayReport   l (toSys r) (toSys r′) (allRelayAdv-of  (toSys r) (toSys r′))
      )

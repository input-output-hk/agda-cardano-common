{-# OPTIONS --safe #-}

-- Exhaustive full node-policy compatibility for two typed endpoint prefixes.
-- External input facts are existential source witnesses, not deployment assertions.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverDecide
  (Notification : Set) (notificationEq : DecidableEquality Notification)
  (representative : Notification) where

open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Projection
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBridge Notification as Reduction
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeBasisAdequacy Notification as Adequacy
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverWireReplay Notification notificationEq as Replay
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Notification notificationEq representative as Existing
import Semantics.Replay.TwoList as TwoList
import Semantics.Replay.TwoListDecide as TwoListDecide

-- The independent original language retains each merge, complete input witness and full node target.
SourceTrace : List Rows.ClientRow → List Rows.ServerRow → Set
SourceTrace client server = Σ[ events ∈ List D.Event ]
  (Rows.Merge client server events × Σ[ target ∈ Node.State ] Reduction.SourceRun Node.initial events target)

-- Every full node witness also obeys the existing broader generic nodeNext driver specification.
generic-source : ∀ {client server} → SourceTrace client server → Existing.SourceTrace S.nodeNext client server
generic-source (events , merged , target , actions , source , observed) =
  events , merged , Node.driverState target ,
  subst (λ rows → D.Run S.nodeNext D.initial rows (Node.driverState target)) observed (Projection.driver source)

-- Both whole endpoint inputs fix the finite payload basis before any hidden or merge search.
module For (client : List Rows.ClientRow) (server : List Rows.ServerRow) where
  module A = Adequacy.ForInput notificationEq representative (Rows.input client server)
  module E = Replay A.basis
  module Pair = TwoList.Traces E.replay Rows.clientEvent Rows.serverEvent
  module Search = TwoListDecide.Decider E.replay Rows.clientEvent Rows.serverEvent E.tau-accessible

  -- Original merge evidence has exactly the generic engine's two endpoint choices.
  to-merge : ∀ {cs ss events} → Rows.Merge cs ss events → Pair.Merge cs ss events
  to-merge Rows.empty = Pair.empty
  to-merge (Rows.client merged) = Pair.client (to-merge merged)
  to-merge (Rows.server merged) = Pair.server (to-merge merged)

  -- Recovering a merge never reclassifies endpoint agency or inserts a visible row.
  from-merge : ∀ {cs ss events} → Pair.Merge cs ss events → Rows.Merge cs ss events
  from-merge Pair.empty = Rows.empty
  from-merge (Pair.client merged) = Rows.client (from-merge merged)
  from-merge (Pair.server merged) = Rows.server (from-merge merged)

  -- Basis adequacy preserves each observed value and every source merge of the fixed inputs.
  source→replay : SourceTrace client server → Pair.PairTrace Core.initial client server
  source→replay (events , merged , target , original) with
    A.node→basis-covered (Rows.covered merged) (target , original)
  ... | reached , restricted = Pair.from-merged
    (events , to-merge merged , reached , E.from-run restricted)

  -- Every replay result rehydrates to a genuine full source node-policy run.
  replay→source : Pair.PairTrace Core.initial client server → SourceTrace client server
  replay→source witness with Pair.to-merged witness
  ... | events , merged , target , run with A.basis→node (target , E.to-run run)
  ...   | originalTarget , original = events , from-merge merged , originalTarget , original

  -- Both complete finite languages coincide; no scheduling, payload or merge alternatives are dropped.
  equivalence : (SourceTrace client server → Pair.PairTrace Core.initial client server) ×
    (Pair.PairTrace Core.initial client server → SourceTrace client server)
  equivalence = source→replay , replay→source

  -- The shared complete two-list engine accepts with a witness or refutes every permitted source run.
  check : Dec (SourceTrace client server)
  check with Search.decide client server Core.initial
  ... | yes witness = yes (replay→source witness)
  ... | no absent = no λ source → absent (source→replay source)

-- Existing cheap necessary guards refute only traces already impossible in the broader generic model.
decide : (client : List Rows.ClientRow) (server : List Rows.ServerRow) → Dec (SourceTrace client server)
decide client server with Existing.all-prechecks? S.nodeNext client server
... | no absent = no λ source → absent (Existing.all-precheck-necessary (generic-source source))
... | yes _ = For.check client server

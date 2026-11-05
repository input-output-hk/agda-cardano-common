{-# OPTIONS --safe #-}

-- Exhaustive compatibility of two typed endpoint prefixes for the unchanged generic driver model.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide
  (Notification : Set) (notificationEq : DecidableEquality Notification)
  (representative : Notification) where

open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Notification ⊤ as Basis
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecutionReplay Notification notificationEq as Engine
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ReadyGateOrder Notification notificationEq as Ordering
import Cardano_network.Replay.LeiosNotifyPipeLookahead.UniqueBasisAdequacy Notification ⊤ as Adequacy
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LocalPrecheck Notification ⊤ as Local
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheck Notification ⊤ as Packets
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketCountPrecheck Notification ⊤ as Counts
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CreditPrecheck Notification ⊤ as Credit
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownPrecheck Notification ⊤ as Shutdown
import Semantics.Replay.TwoList as TwoList
import Semantics.Replay.TwoListDecide as TwoListDecide

-- This proposition mentions only the original source model and an exact order-preserving merge.
SourceTrace : S.Contract → List Rows.ClientRow → List Rows.ServerRow → Set
SourceTrace contract client server = Σ[ events ∈ List D.Event ]
  (Rows.Merge client server events × Σ[ target ∈ D.State ] D.Run contract D.initial events target)

-- Local validity and common packet prefixes alone can still permit impossible pending-hook counts.
BasePrechecks : S.Contract → List Rows.ClientRow → List Rows.ServerRow → Set
BasePrechecks contract client server = Local.Pass contract client server × Packets.Pass client server

-- Every unrestricted source witness passes both exact local languages and packet-prefix comparisons.
base-precheck-necessary : ∀ {contract client server} → SourceTrace contract client server →
  BasePrechecks contract client server
base-precheck-necessary (_ , merged , _ , source) =
  Local.necessary merged source , Packets.necessary merged source

-- The two original cheap decisions remain available for independent insufficiency regressions.
base-prechecks? : (contract : S.Contract) (client : List Rows.ClientRow) (server : List Rows.ServerRow) →
  Dec (BasePrechecks contract client server)
base-prechecks? contract client server =
  Local.decide contract client server ×-dec Packets.decide notificationEq client server

-- All three conditions are necessary; their success is never a paired acceptance certificate.
Prechecks : S.Contract → List Rows.ClientRow → List Rows.ServerRow → Set
Prechecks contract client server = BasePrechecks contract client server × Counts.Pass client server

-- One pending Send can explain at most one extra recorded Receive in each channel direction.
precheck-necessary : ∀ {contract client server} → SourceTrace contract client server →
  Prechecks contract client server
precheck-necessary witness@(_ , merged , _ , source) =
  base-precheck-necessary witness , Counts.necessary merged source

-- Cheap certified conditions run before any complete paired search or callback-basis enumeration.
prechecks? : (contract : S.Contract) (client : List Rows.ClientRow) (server : List Rows.ServerRow) →
  Dec (Prechecks contract client server)
prechecks? contract client server =
  base-prechecks? contract client server ×-dec Counts.decide client server

-- The original three predicates stay available; actual reply credit is a further necessary condition.
FullPrechecks : S.Contract → List Rows.ClientRow → List Rows.ServerRow → Set
FullPrechecks contract client server = Prechecks contract client server × Credit.Pass client server

-- Every original fresh source witness also accounts for its peer's recorded Request receives.
full-precheck-necessary : ∀ {contract client server} → SourceTrace contract client server →
  FullPrechecks contract client server
full-precheck-necessary source@(_ , merged , _ , run) =
  precheck-necessary source , Credit.necessary merged run

-- Reply-credit comparison excludes Done and Quit, and needs no notification comparison.
full-prechecks? : (contract : S.Contract) (client : List Rows.ClientRow) (server : List Rows.ServerRow) →
  Dec (FullPrechecks contract client server)
full-prechecks? contract client server =
  prechecks? contract client server ×-dec Credit.decide client server

-- The four-guard interface remains intact; recorded Done additionally needs the peer's recorded Quit.
AllPrechecks : S.Contract → List Rows.ClientRow → List Rows.ServerRow → Set
AllPrechecks contract client server = FullPrechecks contract client server × Shutdown.Pass client server

-- The physical Done origin and source reader phase establish shutdown causality for the original run.
all-precheck-necessary : ∀ {contract client server} → SourceTrace contract client server →
  AllPrechecks contract client server
all-precheck-necessary source@(_ , merged , _ , run) =
  full-precheck-necessary source , Shutdown.necessary merged run

-- This extra constructor-only decision requires neither payload equality nor recorded Send-Done.
all-prechecks? : (contract : S.Contract) (client : List Rows.ClientRow) (server : List Rows.ServerRow) →
  Dec (AllPrechecks contract client server)
all-prechecks? contract client server =
  full-prechecks? contract client server ×-dec Shutdown.decide client server

-- The finite callback basis is fixed from both entire inputs before searching any merge.
module For (contract : S.Contract) (client : List Rows.ClientRow) (server : List Rows.ServerRow) where
  module A = Adequacy.ForInput notificationEq representative (Rows.input client server)
  module B = Basis A.basis
  module E = Engine A.basis
  module Machine = E.For contract
  module Pair = TwoList.Traces (E.replay contract) Rows.clientEvent Rows.serverEvent
  module Order = Ordering A.basis
  module Search = TwoListDecide.OrderedDecider (E.replay contract)
    Rows.clientEvent Rows.serverEvent Machine.tau-accessible
    (Order.orderedTargets contract)
    (λ {s} {cs} {ss} → Order.target-sound {p = contract} {s = s} {client = cs} {server = ss})
    (λ {s} {cs} {ss} → Order.target-complete {p = contract} {s = s} {client = cs} {server = ss})

  -- The source merge witness has exactly the same choices as the generic two-list relation.
  to-merge : ∀ {cs ss events} → Rows.Merge cs ss events → Pair.Merge cs ss events
  to-merge Rows.empty = Pair.empty
  to-merge (Rows.client merged) = Pair.client (to-merge merged)
  to-merge (Rows.server merged) = Pair.server (to-merge merged)

  -- Generic merge evidence cannot introduce any foreign endpoint event.
  from-merge : ∀ {cs ss events} → Pair.Merge cs ss events → Rows.Merge cs ss events
  from-merge Pair.empty = Rows.empty
  from-merge (Pair.client merged) = Rows.client (from-merge merged)
  from-merge (Pair.server merged) = Rows.server (from-merge merged)

  -- A matching unrestricted run is renamed only at hidden unobserved normal selections.
  source→basis : SourceTrace contract client server → Pair.PairTrace D.initial client server
  source→basis (events , merged , target , source) = Pair.from-merged
    (events , to-merge merged , A.M.state target ,
      Machine.from-run (A.adequate-covered (Rows.covered merged) source))

  -- Every restricted-search witness is a genuine unrestricted fresh source execution.
  basis→source : Pair.PairTrace D.initial client server → SourceTrace contract client server
  basis→source witness with Pair.to-merged witness
  ... | events , merged , target , run =
    events , from-merge merged , target , B.sound (Machine.to-run run)

  -- Whole-input adequacy connects the finite search to the unrestricted source language both ways.
  equivalence : (SourceTrace contract client server → Pair.PairTrace D.initial client server) ×
    (Pair.PairTrace D.initial client server → SourceTrace contract client server)
  equivalence = source→basis , basis→source

  -- Failure refutes every source schedule and every permitted merge, never an exhausted budget.
  check : Dec (SourceTrace contract client server)
  check with Search.decide client server D.initial
  ... | yes witness = yes (basis→source witness)
  ... | no absent = no λ source → absent (source→basis source)

-- A failed necessary check refutes the original source language; success still invokes complete search.
decide : (contract : S.Contract) (client : List Rows.ClientRow) (server : List Rows.ServerRow) →
  Dec (SourceTrace contract client server)
decide contract client server with all-prechecks? contract client server
... | no impossible = no λ source → impossible (all-precheck-necessary source)
... | yes _ = For.check contract client server

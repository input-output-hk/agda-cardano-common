{-# OPTIONS --safe #-}

-- Heterogeneous fixed manifests for independent prototype mini-protocol sessions.
module Cardano_network.Replay.Sessions where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (Dec)
open import Semantics.Replay
open import Semantics.Replay.Interleave using (module Product)
import Semantics.Replay.Empty as Empty
open import Cardano_network.Replay.Common public
import Cardano_network.Replay.LeiosFetchSession as Fetch
import Cardano_network.Replay.LeiosFetchInterleaved as FetchCheck
import Cardano_network.Replay.LeiosNotifyPipeline as Notify
import Cardano_network.Replay.BlockFetchClientSession as BlockFetch
import Cardano_network.Replay.BlockFetchServerSession as BlockFetchServer
import Cardano_network.Replay.ChainSyncSession as ChainSync
import Cardano_network.Replay.TxSubmission2Session as TxSubmission2

-- A protocol and role select one independently initialized generation.
data Session : Set where
  fetch notify blockfetch chainsync txsubmission2 : Role → Session

-- Component state type selected by the manifest.
LocalState : Session → Set
LocalState (fetch _) = Fetch.St
LocalState (notify _) = Notify.St
LocalState (blockfetch client) = BlockFetch.St
LocalState (blockfetch server) = BlockFetchServer.St
LocalState (chainsync _) = ChainSync.St
LocalState (txsubmission2 _) = TxSubmission2.St

-- Component event type prevents cross-protocol message confusion.
LocalEvent : Session → Set
LocalEvent (fetch _) = Fetch.E
LocalEvent (notify _) = Notify.E
LocalEvent (blockfetch _) = BlockFetch.E
LocalEvent (chainsync _) = ChainSync.E
LocalEvent (txsubmission2 _) = TxSubmission2.E

-- The per-session initial state, before any observed wire events.
start : (s : Session) → LocalState s
start (fetch r) = FetchCheck.start r
start (notify r) = Notify.idle
start (blockfetch client) = BlockFetch.initial
start (blockfetch server) = BlockFetchServer.idle
start (chainsync _) = ChainSync.initial
start (txsubmission2 _) = TxSubmission2.initial

-- Independent protocol bounds; TxSubmission2 pipelines on the server role.
localModelWithProtocolDepths : (k depth bfDepth csDepth tsDepth : ℕ) (s : Session) → Replay 0ℓ (LocalState s) (LocalEvent s)
localModelWithProtocolDepths k depth bfDepth csDepth tsDepth (fetch _) = Fetch.Spec.leiosFetch k
localModelWithProtocolDepths k depth bfDepth csDepth tsDepth (notify r) = Notify.Spec.leiosNotify depth r
localModelWithProtocolDepths k depth bfDepth csDepth tsDepth (blockfetch client) = BlockFetch.Spec.model bfDepth
localModelWithProtocolDepths k depth bfDepth csDepth tsDepth (blockfetch server) = BlockFetchServer.model
localModelWithProtocolDepths k depth bfDepth csDepth tsDepth (chainsync r) = ChainSync.Spec.model csDepth r
localModelWithProtocolDepths k depth bfDepth csDepth tsDepth (txsubmission2 r) = TxSubmission2.Spec.model tsDepth r

-- Reuse the certified component decision procedures.
localCheckWithProtocolDepths : (k depth bfDepth csDepth tsDepth : ℕ) (s : Session) (es : List (LocalEvent s)) →
             Dec (Traces.HasTrace (localModelWithProtocolDepths k depth bfDepth csDepth tsDepth s) (start s) es)
localCheckWithProtocolDepths k depth bfDepth csDepth tsDepth (fetch r) = FetchCheck.local? k r
localCheckWithProtocolDepths k depth bfDepth csDepth tsDepth (notify r) = Notify.Spec.check depth r
localCheckWithProtocolDepths k depth bfDepth csDepth tsDepth (blockfetch client) = BlockFetch.Spec.check bfDepth
localCheckWithProtocolDepths k depth bfDepth csDepth tsDepth (blockfetch server) = BlockFetchServer.check
localCheckWithProtocolDepths k depth bfDepth csDepth tsDepth (chainsync r) = ChainSync.Spec.check csDepth r
localCheckWithProtocolDepths k depth bfDepth csDepth tsDepth (txsubmission2 r) = TxSubmission2.Spec.check tsDepth r

-- State of the finite heterogeneous product.
States : List Session → Set
States [] = ⊤
States (s ∷ ss) = LocalState s × States ss

-- Nested tags select the component's own event type.
Events : List Session → Set
Events [] = ⊥
Events (s ∷ ss) = LocalEvent s ⊎ Events ss

-- Fold the generic product without changing its semantics or proof.
modelWithProtocolDepths : (k depth bfDepth csDepth tsDepth : ℕ) (ss : List Session) → Replay 0ℓ (States ss) (Events ss)
modelWithProtocolDepths k depth bfDepth csDepth tsDepth [] = Empty.empty
modelWithProtocolDepths k depth bfDepth csDepth tsDepth (s ∷ ss) = Product.interleave (localModelWithProtocolDepths k depth bfDepth csDepth tsDepth s) (modelWithProtocolDepths k depth bfDepth csDepth tsDepth ss)

-- Initialize every generation in the manifest independently.
initial : (ss : List Session) → States ss
initial [] = tt
initial (s ∷ ss) = start s , initial ss

-- A decision carries a global run or a refutation of all global runs.
checkWithProtocolDepths : (k depth bfDepth csDepth tsDepth : ℕ) (ss : List Session) (es : List (Events ss)) →
        Dec (Traces.HasTrace (modelWithProtocolDepths k depth bfDepth csDepth tsDepth ss) (initial ss) es)
checkWithProtocolDepths k depth bfDepth csDepth tsDepth [] = Empty.empty?
checkWithProtocolDepths k depth bfDepth csDepth tsDepth (s ∷ ss) = Product.decide (localModelWithProtocolDepths k depth bfDepth csDepth tsDepth s) (modelWithProtocolDepths k depth bfDepth csDepth tsDepth ss) (localCheckWithProtocolDepths k depth bfDepth csDepth tsDepth s) (checkWithProtocolDepths k depth bfDepth csDepth tsDepth ss)

-- Preserve the four-bound local model API with requester capacity four.
localModelWithAllDepths : (k depth bfDepth csDepth : ℕ) (s : Session) → Replay 0ℓ (LocalState s) (LocalEvent s)
localModelWithAllDepths k depth bfDepth csDepth = localModelWithProtocolDepths k depth bfDepth csDepth 4

-- Compatibility local decision for existing callers.
localCheckWithAllDepths : (k depth bfDepth csDepth : ℕ) (s : Session) (es : List (LocalEvent s)) →
  Dec (Traces.HasTrace (localModelWithAllDepths k depth bfDepth csDepth s) (start s) es)
localCheckWithAllDepths k depth bfDepth csDepth = localCheckWithProtocolDepths k depth bfDepth csDepth 4

-- Preserve the four-bound product API.
modelWithAllDepths : (k depth bfDepth csDepth : ℕ) (ss : List Session) → Replay 0ℓ (States ss) (Events ss)
modelWithAllDepths k depth bfDepth csDepth = modelWithProtocolDepths k depth bfDepth csDepth 4

-- Preserve the four-bound product decider API.
checkWithAllDepths : (k depth bfDepth csDepth : ℕ) (ss : List Session) (es : List (Events ss)) →
  Dec (Traces.HasTrace (modelWithAllDepths k depth bfDepth csDepth ss) (initial ss) es)
checkWithAllDepths k depth bfDepth csDepth = checkWithProtocolDepths k depth bfDepth csDepth 4

-- Preserve the three-bound local model API with ChainSync depth 300.
localModelWithDepths : (k depth bfDepth : ℕ) (s : Session) → Replay 0ℓ (LocalState s) (LocalEvent s)
localModelWithDepths k depth bfDepth = localModelWithAllDepths k depth bfDepth 300

-- Preserve the three-bound local decision API.
localCheckWithDepths : (k depth bfDepth : ℕ) (s : Session) (es : List (LocalEvent s)) →
  Dec (Traces.HasTrace (localModelWithDepths k depth bfDepth s) (start s) es)
localCheckWithDepths k depth bfDepth = localCheckWithAllDepths k depth bfDepth 300

-- Preserve the three-bound product model API.
modelWithDepths : (k depth bfDepth : ℕ) (ss : List Session) → Replay 0ℓ (States ss) (Events ss)
modelWithDepths k depth bfDepth = modelWithAllDepths k depth bfDepth 300

-- Preserve the three-bound product decision API.
checkWithDepths : (k depth bfDepth : ℕ) (ss : List Session) (es : List (Events ss)) →
  Dec (Traces.HasTrace (modelWithDepths k depth bfDepth ss) (initial ss) es)
checkWithDepths k depth bfDepth = checkWithAllDepths k depth bfDepth 300

-- Compatibility interface: original two bounds, BlockFetch client depth 100.
localModelWithDepth : (k depth : ℕ) (s : Session) → Replay 0ℓ (LocalState s) (LocalEvent s)
localModelWithDepth k depth = localModelWithDepths k depth 100

-- Preserve the original local decider signature.
localCheckWithDepth : (k depth : ℕ) (s : Session) (es : List (LocalEvent s)) →
  Dec (Traces.HasTrace (localModelWithDepth k depth s) (start s) es)
localCheckWithDepth k depth = localCheckWithDepths k depth 100

-- Preserve the original product model signature.
modelWithDepth : (k depth : ℕ) (ss : List Session) → Replay 0ℓ (States ss) (Events ss)
modelWithDepth k depth = modelWithDepths k depth 100

-- Preserve the original product decider signature.
checkWithDepth : (k depth : ℕ) (ss : List Session) (es : List (Events ss)) →
  Dec (Traces.HasTrace (modelWithDepth k depth ss) (initial ss) es)
checkWithDepth k depth = checkWithDepths k depth 100

-- Preserve the original API with a depth-one Notify default.
model : (k : ℕ) (ss : List Session) → Replay 0ℓ (States ss) (Events ss)
model k = modelWithDepth k 1

-- The compatibility decider retains the previous Notify bound.
check : (k : ℕ) (ss : List Session) (es : List (Events ss)) →
        Dec (Traces.HasTrace (model k ss) (initial ss) es)
check k = checkWithDepth k 1

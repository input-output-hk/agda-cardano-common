{-# OPTIONS --safe #-}

-- The production policy inherits strict hidden descent without erasing its state/queue guards.
module Cardano_network.LeiosNotifyPipeLookahead.NodeScheduling (Notification : Set) where

open import Data.Nat using (ℕ; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using ([])
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc; acc)
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Projection
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification ⊤ as Cost
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingRank Notification ⊤ as Rank
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification ⊤ as Shutdown

-- Queue contents and input snapshots do not hide an uncounted scheduling loop.
rank : Node.State → ℕ
rank s = Cost.rank (Node.driverState s)

-- Each real node hidden step projects to one strictly decreasing paired hidden step.
decreases : ∀ {s t} → Node.Tau s t → rank t < rank s
decreases pr = Rank.decreases (Projection.driver-tau pr)

-- Natural well-foundedness lifts to the full production-policy state.
from-rank : ∀ s → Acc _<_ (rank s) → Acc (λ t s → Node.Tau s t) s
from-rank s (acc smaller) = acc λ {t} pr → from-rank t (smaller (decreases pr))

-- Hidden scheduling is finite at every node state, even with arbitrary finite stored queues.
tau-accessible : ∀ s → Acc (λ t s → Node.Tau s t) s
tau-accessible s = from-rank s (<-wellFounded (rank s))

-- Empty full-action histories contain only actual node hidden steps.
hidden-steps : ∀ {s t} → Node.Run s [] t → ℕ
hidden-steps Node.stop = 0
hidden-steps (Node.internal _ run) = suc (hidden-steps run)

-- The initial potential bounds every such finite hidden path.
hidden-bounded : ∀ {s t} (run : Node.Run s [] t) → hidden-steps run ≤ rank s
hidden-bounded Node.stop = z≤n
hidden-bounded (Node.internal pr run) = ≤-trans (s≤s (hidden-bounded run)) (decreases pr)

-- Count projected protocol operations, excluding stuttering environment/input records.
driver-operations : ∀ {s actions t} → Node.Run s actions t → ℕ
driver-operations run = Shutdown.steps (Projection.driver run)

-- Once both peers stop, projected driver work is bounded even through policy/input interleavings.
shutdown-bounded : ∀ {s actions t} (run : Node.Run s actions t) →
  Shutdown.BothStopping (Node.driverState s) → driver-operations run ≤ rank s
shutdown-bounded run = Shutdown.bounded (Projection.driver run)

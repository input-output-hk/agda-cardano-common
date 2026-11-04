{-# OPTIONS --guardedness #-}

-- Fresh source/native/runtime applications of general server-drain progress.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerDrainNativeTests where

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.List using (List; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Projection
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤ as Raw
import Cardano_network.LeiosNotifyPipeLookahead.ServerDrain Notification ⊤ as Drain
import Cardano_network.LeiosNotifyPipeLookahead.ServerProgress Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Notification ⊤ as Runtime
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification ⊤ as Work
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification ⊤ as Cost
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerDrainBridge exactParams ⊤ as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownNativeTests as Fixture
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ProgressNativeTests as Execution
open Raw using (module Traces)

-- Endpoint coordinates and callback contract are those of the existing fresh node fixture.
module Proof = Bridge.At S.nodeNext fzero fzero hi hi

-- Fresh reachability supplies all structural server-progress premises at this actual prefix.
native-completion : Proof.Certificate (Node.driverState Fixture.before-done)
native-completion = Proof.from-source (Projection.driver Fixture.prefix) (refl , refl)

-- An actual native prefix also reconstructs a source state with its conditional continuation.
native-inversion : Σ[ raw ∈ D.State ]
  (Proof.Tree.tree (Node.driverState Fixture.before-done) ≡ Proof.Tree.tree raw ×
    (Work.BothStopping raw → Proof.Certificate raw))
native-inversion = Proof.from-native Fixture.native-prefix

-- This runtime's Receive-Done then Send-Done sequence responds until the server is closed.
server-responsive : Runtime.Responsive Drain.Closed Execution.execution
server-responsive zero unfinished = Runtime.now Runtime.advanced
server-responsive (suc zero) unfinished = Runtime.now Runtime.advanced
server-responsive (suc (suc n)) unfinished = ⊥-elim (unfinished Server.closed)

-- The fresh runtime theorem needs responsiveness/failure conditions, but no structural axiom.
native-runtime : Σ[ k ∈ ℕ ] Σ[ rows ∈ List D.Event ] Σ[ trace ∈
  (Proof.Tree.tree (Runtime.state Execution.execution zero) Traces.⟹∖√⟨ map Proof.Tree.encode rows ⟩
    Proof.Tree.tree (Runtime.state Execution.execution k)) ]
  (zero ≤ k × Drain.Closed (Runtime.state Execution.execution k) ×
    Proof.Bound.steps trace ≤ Cost.rank (Runtime.state Execution.execution zero))
native-runtime = Proof.runtime-from-source Execution.execution server-responsive
  Execution.no-failure Execution.maximal zero (Projection.driver Fixture.prefix) (refl , refl)

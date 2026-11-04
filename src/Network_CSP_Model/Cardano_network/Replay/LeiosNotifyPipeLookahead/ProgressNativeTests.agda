{-# OPTIONS --guardedness #-}

-- Conditional completion instantiated at an actual fresh native Done race.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ProgressNativeTests where

open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.List using (List; map)
open import Data.Product using (Σ-syntax; _×_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (refl)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification ⊤ as P
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Notification ⊤ as R
import Cardano_network.LeiosNotifyPipeLookahead.DoneProgress Notification ⊤ as H
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification ⊤ as Cost
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤ as Raw
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ProgressBridge exactParams ⊤ as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownNativeTests as Fixture
open Raw using (module Traces)

-- The unchanged callback contract and endpoint tags match the fresh native fixture.
module Native = Bridge.At S.nodeNext fzero fzero hi hi
-- Concrete structural progress discharges the abstract local-progress parameter here.
module Proof = Native.Conditional H.Handoff (H.local-progress S.nodeNext)

-- The fresh prefix ends after physical Done decode, before either trace hook is published.
handoff : H.Handoff (Node.driverState Fixture.before-done)
handoff = H.decoded-pending

-- Completion constructs an actual native continuation, retaining a quantitative step bound.
native-completion : Σ[ rows ∈ List D.Event ] Σ[ t ∈ D.State ] Σ[ trace ∈
  (Native.Tree.tree (Node.driverState Fixture.before-done)
    Traces.⟹∖√⟨ map Native.Tree.encode rows ⟩ Native.Tree.tree t) ]
  (P.Clean t × Native.Bound.steps trace ≤ Cost.rank (Node.driverState Fixture.before-done))
native-completion = Proof.complete handoff (H.both-stopping handoff)

-- This runtime records Receive-Done before the delayed Send-Done, as the source permits.
execution : R.Execution S.nodeNext
R.state execution zero = Node.driverState Fixture.before-done
R.state execution (suc zero) = Node.driverState Fixture.after-done
R.state execution (suc (suc n)) = Fixture.closed
R.tick execution zero = R.advance (P.wire (D.clientReceived C.receivedDone))
R.tick execution (suc zero) = R.advance (P.wire (D.serverSent S.finish))
R.tick execution (suc (suc n)) = R.waiting
R.link execution zero = refl
R.link execution (suc zero) = refl
R.link execution (suc (suc n)) = refl

-- Both outstanding hooks respond; there is no latency premise after the clean target.
responsive : R.Responsive P.Clean execution
responsive zero unfinished = R.now R.advanced
responsive (suc zero) unfinished = R.now R.advanced
responsive (suc (suc n)) unfinished = ⊥-elim (unfinished P.clean)

-- This concrete schedule supplies the no-failure premise constructively.
no-failure : R.NoFailure execution
no-failure zero fault ()
no-failure (suc zero) fault ()
no-failure (suc (suc n)) fault ()

-- No premature terminal observation occurs in the concrete schedule.
maximal : R.Maximal execution
maximal zero ()
maximal (suc zero) ()
maximal (suc (suc n)) ()

-- Actual runtime liveness also produces its corresponding native finite path and bound.
native-runtime-completion : Σ[ k ∈ ℕ ] Σ[ rows ∈ List D.Event ] Σ[ trace ∈
  (Native.Tree.tree (R.state execution zero) Traces.⟹∖√⟨ map Native.Tree.encode rows ⟩
    Native.Tree.tree (R.state execution k)) ]
  (zero ≤ k × P.Clean (R.state execution k) × Native.Bound.steps trace ≤ Cost.rank (R.state execution zero))
native-runtime-completion = Proof.runtime-complete execution responsive no-failure maximal zero
  handoff (H.both-stopping handoff)

{-# OPTIONS --guardedness #-}

-- Conditional completion produces actual native paired traces, not just source reachability.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ProgressBridge (p : Params) (Return : Set) where

open import Data.Nat using (ℕ; _≤_)
open import Data.List using (List; map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return as Native
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification Return as Cost
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Work
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification Return as Model
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Notification Return as Runtime
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p Return as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingBridge p Return as Scheduling

-- Endpoint coordinates and callback policy are fixed throughout each native completion path.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  -- The source-to-native introduction retains actual wire labels and hidden operations.
  module Tree = Native.At contract cl sl cd sd
  -- Existing exact realization supplies the native finite path.
  module B = Bridge.At contract cl sl cd sd
  -- Its quantitative bound counts actual native transitions.
  module Bound = Scheduling.At contract cl sl cd sd
  open Native using (module Traces)

  -- The invariant and its structural local progress remain visible theorem parameters.
  module Conditional (Invariant : D.State → Set)
    (progress : Model.LocalProgress contract Model.Clean Invariant) where

    -- Constructive model completion is proved by the checked decreasing potential.
    module Source = Model.With contract Model.Clean Invariant progress

    -- Model existence lifts to an actual bounded native path ending with empty work/hooks.
    complete : ∀ {s} → Invariant s → Work.BothStopping s →
      Σ[ rows ∈ List D.Event ] Σ[ t ∈ D.State ] Σ[ trace ∈
        (Tree.tree s Traces.⟹∖√⟨ map Tree.encode rows ⟩ Tree.tree t) ]
        (Model.Clean t × Bound.steps trace ≤ Cost.rank s)
    complete invariant both with Source.complete invariant both
    ... | Model.completion rows t run reached bounded =
      rows , t , B.realize run , reached , Bound.shutdown-bounded (B.realize run) both

    -- The runtime theorem keeps responsiveness, failures and terminal observations explicit.
    runtime-complete : (ex : Runtime.Execution contract) → Runtime.Responsive Model.Clean ex →
      Runtime.NoFailure ex → Runtime.Maximal ex → ∀ n → Invariant (Runtime.state ex n) →
      Work.BothStopping (Runtime.state ex n) →
      Σ[ k ∈ ℕ ] Σ[ rows ∈ List D.Event ] Σ[ trace ∈
        (Tree.tree (Runtime.state ex n) Traces.⟹∖√⟨ map Tree.encode rows ⟩ Tree.tree (Runtime.state ex k)) ]
        (n ≤ k × Model.Clean (Runtime.state ex k) × Bound.steps trace ≤ Cost.rank (Runtime.state ex n))
    runtime-complete ex responsive noFailure maximal n invariant both
      with Runtime.With.complete contract Model.Clean Invariant progress ex responsive noFailure maximal n invariant both
    ... | Runtime.eventual k later rows run reached bounded =
      k , rows , B.realize run , later , reached , Bound.shutdown-bounded (B.realize run) both

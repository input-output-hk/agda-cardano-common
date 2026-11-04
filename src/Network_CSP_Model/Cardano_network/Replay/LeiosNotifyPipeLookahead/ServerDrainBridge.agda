{-# OPTIONS --guardedness #-}

-- Fresh server progress yields actual native continuations with no structural-progress premise.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerDrainBridge (p : Params) (Return : Set) where

open import Data.List using (List; map)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return as Native
import Cardano_network.LeiosNotifyPipeLookahead.ServerDrain Notification Return as Drain
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification Return as Source
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Notification Return as Runtime
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Work
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification Return as Cost
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p Return as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingBridge p Return as Scheduling

-- Native endpoint coordinates stay fixed while all driver interleavings remain available.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  -- The native paired process is unchanged by this progress theorem.
  module Tree = Native.At contract cl sl cd sd
  -- Existing two-sided finite trace correspondence supplies exact source targets.
  module B = Bridge.At contract cl sl cd sd
  -- Actual native operation counts retain the earlier quantitative bound.
  module Bound = Scheduling.At contract cl sl cd sd
  open Native using (module Traces)

  -- This certificate closes the server; client work and response packets may still remain.
  Certificate : D.State → Set₁
  Certificate s = Σ[ rows ∈ List D.Event ] Σ[ t ∈ D.State ] Σ[ trace ∈
    (Tree.tree s Traces.⟹∖√⟨ map Tree.encode rows ⟩ Tree.tree t) ]
    (Drain.Closed t × Bound.steps trace ≤ Cost.rank s)

  -- Fresh reachability discharges the structural phase and pending-Send obligations.
  from-source : ∀ {rows s} → D.Run contract D.initial rows s → Work.BothStopping s → Certificate s
  from-source prefix both with Drain.fresh-complete prefix both
  ... | Source.completion rows t run reached bounded =
    rows , t , B.realize run , reached , Bound.shutdown-bounded (B.realize run) both

  -- Inversion retains the reconstructed source state rather than assuming tree injectivity.
  from-native : ∀ {es} {P : Native.Proc} → Tree.tree D.initial Traces.⟹∖√⟨ es ⟩ P →
    Σ[ s ∈ D.State ] (P ≡ Tree.tree s × (Work.BothStopping s → Certificate s))
  from-native prefix with B.sound prefix
  ... | rows , s , matching , source , same = s , same , from-source source

  -- Given runtime responsiveness/failure premises, fresh reachability suffices for server liveness.
  runtime-from-source : (ex : Runtime.Execution contract) → Runtime.Responsive Drain.Closed ex →
    Runtime.NoFailure ex → Runtime.Maximal ex → ∀ n {prefixRows} →
    D.Run contract D.initial prefixRows (Runtime.state ex n) → Work.BothStopping (Runtime.state ex n) →
    Σ[ k ∈ ℕ ] Σ[ rows ∈ List D.Event ] Σ[ trace ∈
      (Tree.tree (Runtime.state ex n) Traces.⟹∖√⟨ map Tree.encode rows ⟩ Tree.tree (Runtime.state ex k)) ]
      (n ≤ k × Drain.Closed (Runtime.state ex k) × Bound.steps trace ≤ Cost.rank (Runtime.state ex n))
  runtime-from-source ex responsive noFailure maximal n prefix both
    with Drain.fresh-runtime-complete ex responsive noFailure maximal n prefix both
  ... | Runtime.eventual k later rows run reached bounded =
    k , rows , B.realize run , later , reached , Bound.shutdown-bounded (B.realize run) both

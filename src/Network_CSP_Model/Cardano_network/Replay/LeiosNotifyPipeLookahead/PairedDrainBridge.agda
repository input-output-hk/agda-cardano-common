{-# OPTIONS --guardedness #-}

-- General fresh paired completion supplies actual native finite continuations and runtime paths.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedDrainBridge (p : Params) (Return : Set) where

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
import Cardano_network.LeiosNotifyPipeLookahead.PairedDrain Notification Return as Drain
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification Return as Source
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Notification Return as Runtime
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Work
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification Return as Cost
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p Return as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingBridge p Return as Scheduling

-- Source/native coordinates and callback contract remain fixed across every continuation.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  -- The same unchanged native paired source model is the target of these certificates.
  module Tree = Native.At contract cl sl cd sd
  -- Existing exact source realization and inversion retain native packet labels.
  module B = Bridge.At contract cl sl cd sd
  -- The count is the actual native hidden-plus-wire path length.
  module Bound = Scheduling.At contract cl sl cd sd
  open Native using (module Traces)

  -- Full paired closure empties both peers, both directional FIFOs and all four trace hooks.
  Certificate : D.State → Set₁
  Certificate s = Σ[ rows ∈ List D.Event ] Σ[ t ∈ D.State ] Σ[ trace ∈
    (Tree.tree s Traces.⟹∖√⟨ map Tree.encode rows ⟩ Tree.tree t) ]
    (Source.Clean t × Bound.steps trace ≤ Cost.rank s)

  -- Fresh reachability now proves the complete paired structural-progress obligations.
  from-source : ∀ {rows s} → D.Run contract D.initial rows s → Work.BothStopping s → Certificate s
  from-source prefix both with Drain.fresh-complete prefix both
  ... | Source.completion rows t run reached bounded =
    rows , t , B.realize run , reached , Bound.shutdown-bounded (B.realize run) both

  -- Native inversion exposes the exact fresh source target without assuming tree injectivity.
  from-native : ∀ {es} {P : Native.Proc} → Tree.tree D.initial Traces.⟹∖√⟨ es ⟩ P →
    Σ[ s ∈ D.State ] (P ≡ Tree.tree s × (Work.BothStopping s → Certificate s))
  from-native prefix with B.sound prefix
  ... | rows , s , matching , source , same = s , same , from-source source

  -- Runtime liveness still requires real responsiveness and failure exclusion, not log EOF.
  runtime-from-source : (ex : Runtime.Execution contract) → Runtime.Responsive Source.Clean ex →
    Runtime.NoFailure ex → Runtime.Maximal ex → ∀ n {prefixRows} →
    D.Run contract D.initial prefixRows (Runtime.state ex n) → Work.BothStopping (Runtime.state ex n) →
    Σ[ k ∈ ℕ ] Σ[ rows ∈ List D.Event ] Σ[ trace ∈
      (Tree.tree (Runtime.state ex n) Traces.⟹∖√⟨ map Tree.encode rows ⟩ Tree.tree (Runtime.state ex k)) ]
      (n ≤ k × Source.Clean (Runtime.state ex k) × Bound.steps trace ≤ Cost.rank (Runtime.state ex n))
  runtime-from-source ex responsive noFailure maximal n prefix both
    with Drain.fresh-runtime-complete ex responsive noFailure maximal n prefix both
  ... | Runtime.eventual k later rows run reached bounded =
    k , rows , B.realize run , later , reached , Bound.shutdown-bounded (B.realize run) both

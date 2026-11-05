{-# OPTIONS --guardedness #-}

-- The generic source obstruction excludes every matching native PTree trace via the existing sound bridge.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CycleObstructionNative (p : Params) where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_)
open import Data.Unit using (⊤)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p using (Notification)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CycleObstruction Notification ⊤ as Cycle
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideNative p as Bridge

-- Links, directions and callback contract are the same fixed coordinates used by the original native bridge.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  module Native = Bridge.At contract cl sl cd sd

  -- Native inversion covers arbitrary actual matching events, without assuming a canonical encoding.
  no-native : (value : Notification) (n : ℕ) → 3 ≤ n →
    Native.NativeTrace (Cycle.client value n) (Cycle.server value n) → ⊥
  no-native value n large native = Cycle.no-source contract value n large (Native.sound native)

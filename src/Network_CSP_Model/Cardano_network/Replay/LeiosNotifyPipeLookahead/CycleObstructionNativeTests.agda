{-# OPTIONS --guardedness #-}

-- Native rejection uses the generic family theorem, without evaluating complete replay.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CycleObstructionNativeTests where

open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([])
open import Data.Nat using (z≤n; s≤s)
open import Data.Unit using (⊤)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (Notification; votes)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CycleObstruction Notification ⊤ as Cycle
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CycleObstructionNative exactParams as Proof

-- The fixture is interpreted at real configured link/direction coordinates under either contract.
module At (contract : S.Contract) where
  module P = Proof.At contract fzero fzero hi hi

  -- Three rounds already exclude every matching native paired PTree execution.
  three-absent : P.Native.NativeTrace (Cycle.client (votes []) 3) (Cycle.server (votes []) 3) → ⊥
  three-absent = P.no-native (votes []) 3 (s≤s (s≤s (s≤s z≤n)))

  -- The same parametric proof applies to larger inputs without additional search normalization.
  four-absent : P.Native.NativeTrace (Cycle.client (votes []) 4) (Cycle.server (votes []) 4) → ⊥
  four-absent = P.no-native (votes []) 4 (s≤s (s≤s (s≤s z≤n)))

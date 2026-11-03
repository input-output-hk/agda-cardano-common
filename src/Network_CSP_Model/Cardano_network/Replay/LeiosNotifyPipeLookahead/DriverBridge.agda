{-# OPTIONS --guardedness #-}

-- Two-sided finite record-trace correspondence for the paired source-operation tree.
-- No normalization of raw logs or refinement of the Haskell implementation is assumed.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverBridge
  (Notification Return : Set) (notificationEq : DecidableEquality Notification) where

open import Data.List using (map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverTree Notification Return notificationEq as T

-- Fix the responder callback message-kind contract while retaining all driver choices.
module For (contract : S.Contract) where
  module Native = T.Native contract

  -- Original operational runs embed without changing endpoint order or payloads.
  to-native-run : ∀ {s es t} → D.Run contract s es t → Native.Run s es t
  to-native-run D.stop = Native.stop
  to-native-run (D.internal pr run) = Native.internal pr (to-native-run run)
  to-native-run (D.visible pr run) = Native.visibleStep pr (to-native-run run)

  -- Recover the original run type from the compiler's generic source execution.
  from-native-run : ∀ {s es t} → Native.Run s es t → D.Run contract s es t
  from-native-run Native.stop = D.stop
  from-native-run (Native.internal pr run) = D.internal pr (from-native-run run)
  from-native-run (Native.visibleStep pr run) = D.visible pr (from-native-run run)

  -- Completeness realizes every paired operational record history in the actual PTree.
  complete : ∀ {s es t} → D.Run contract s es t →
    Native.tree s Native.Traces.⟹∖√⟨ map Native.event es ⟩ Native.tree t
  complete run = Native.run-intro (to-native-run run)

  -- Soundness reconstructs an operational history from every corresponding tree run.
  sound : ∀ {s es P} → Native.tree s Native.Traces.⟹∖√⟨ map Native.event es ⟩ P →
    Σ[ t ∈ D.State ] (D.Run contract s es t × P ≡ Native.tree t)
  sound run with Native.run-elim run
  ... | t , source , eq = t , from-native-run source , eq

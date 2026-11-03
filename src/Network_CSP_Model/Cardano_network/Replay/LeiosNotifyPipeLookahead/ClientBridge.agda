{-# OPTIONS --guardedness #-}

-- Two-sided finite trace correspondence between ClientModel and its source PTree.
-- Events are exact source actions, including callbacks, with no wire projection yet.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientBridge
  (Notification Return : Set) (notificationEq : DecidableEquality Notification) where

open import Data.List using (map)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
open import Cardano_network.LeiosNotifyPipeLookahead.ClientTree Notification Return notificationEq

-- Embed the original source run without changing a visible action or hidden step.
to-native-run : ∀ {s es t} → C.Run s es t → Native.Run s es t
to-native-run C.stop = Native.stop
to-native-run (C.internal pr run) = Native.internal pr (to-native-run run)
to-native-run (C.visible pr run) = Native.visibleStep pr (to-native-run run)

-- Recover the original source-run type from the compiler's generic run type.
from-native-run : ∀ {s es t} → Native.Run s es t → C.Run s es t
from-native-run Native.stop = C.stop
from-native-run (Native.internal pr run) = C.internal pr (from-native-run run)
from-native-run (Native.visibleStep pr run) = C.visible pr (from-native-run run)

-- Completeness realizes every source run in the actual coinductive PTree.
complete : ∀ {s es t} → C.Run s es t →
  Native.tree s Native.Traces.⟹∖√⟨ map Native.event es ⟩ Native.tree t
complete run = Native.run-intro (to-native-run run)

-- Soundness reconstructs a source run from every finite tree run at this observation.
sound : ∀ {s es P} → Native.tree s Native.Traces.⟹∖√⟨ map Native.event es ⟩ P →
  Σ[ t ∈ C.State ] (C.Run s es t × P ≡ Native.tree t)
sound run with Native.run-elim run
... | t , source , eq = t , from-native-run source , eq

{-# OPTIONS --safe #-}

-- Heterogeneous fixed manifests for independent prototype mini-protocol sessions.
module Cardano_network.Replay.Sessions where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (Dec)
open import Semantics.Replay
open import Semantics.Replay.Interleave using (module Product)
import Semantics.Replay.Empty as Empty
open import Cardano_network.Replay.Common public
import Cardano_network.Replay.LeiosFetchSession as Fetch
import Cardano_network.Replay.LeiosFetchInterleaved as FetchCheck
import Cardano_network.Replay.LeiosNotifyPipeline as Notify

-- A protocol and role select one independently initialized generation.
data Session : Set where
  fetch notify : Role → Session

-- Component state type selected by the manifest.
LocalState : Session → Set
LocalState (fetch _) = Fetch.St
LocalState (notify _) = Notify.St

-- Component event type prevents cross-protocol message confusion.
LocalEvent : Session → Set
LocalEvent (fetch _) = Fetch.E
LocalEvent (notify _) = Notify.E

-- The per-session initial state, before any observed wire events.
start : (s : Session) → LocalState s
start (fetch r) = FetchCheck.start r
start (notify r) = Notify.idle

-- Local replay interface; k applies to each Fetch client only.
localModelWithDepth : (k depth : ℕ) (s : Session) → Replay 0ℓ (LocalState s) (LocalEvent s)
localModelWithDepth k depth (fetch _) = Fetch.Spec.leiosFetch k
localModelWithDepth k depth (notify r) = Notify.Spec.leiosNotify depth r

-- Reuse the certified component decision procedures.
localCheckWithDepth : (k depth : ℕ) (s : Session) (es : List (LocalEvent s)) →
             Dec (Traces.HasTrace (localModelWithDepth k depth s) (start s) es)
localCheckWithDepth k depth (fetch r) = FetchCheck.local? k r
localCheckWithDepth k depth (notify r) = Notify.Spec.check depth r

-- State of the finite heterogeneous product.
States : List Session → Set
States [] = ⊤
States (s ∷ ss) = LocalState s × States ss

-- Nested tags select the component's own event type.
Events : List Session → Set
Events [] = ⊥
Events (s ∷ ss) = LocalEvent s ⊎ Events ss

-- Fold the generic product without changing its semantics or proof.
modelWithDepth : (k depth : ℕ) (ss : List Session) → Replay 0ℓ (States ss) (Events ss)
modelWithDepth k depth [] = Empty.empty
modelWithDepth k depth (s ∷ ss) = Product.interleave (localModelWithDepth k depth s) (modelWithDepth k depth ss)

-- Initialize every generation in the manifest independently.
initial : (ss : List Session) → States ss
initial [] = tt
initial (s ∷ ss) = start s , initial ss

-- A decision carries a global run or a refutation of all global runs.
checkWithDepth : (k depth : ℕ) (ss : List Session) (es : List (Events ss)) →
        Dec (Traces.HasTrace (modelWithDepth k depth ss) (initial ss) es)
checkWithDepth k depth [] = Empty.empty?
checkWithDepth k depth (s ∷ ss) = Product.decide (localModelWithDepth k depth s) (modelWithDepth k depth ss) (localCheckWithDepth k depth s) (checkWithDepth k depth ss)

-- Preserve the original API with a depth-one Notify default.
model : (k : ℕ) (ss : List Session) → Replay 0ℓ (States ss) (Events ss)
model k = modelWithDepth k 1

-- The compatibility decider retains the previous Notify bound.
check : (k : ℕ) (ss : List Session) (es : List (Events ss)) →
        Dec (Traces.HasTrace (model k ss) (initial ss) es)
check k = checkWithDepth k 1

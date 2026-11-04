{-# OPTIONS --guardedness #-}

-- Native realization of bounded policy runs, including the full-pipe Quit marker.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ResourceNativeTests where

open import Data.Empty using (⊥)
open import Data.List using (List; map)
open import Data.Nat using (_≤_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Data.Fin using () renaming (zero to fzero)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤ as Native
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as N
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as P
import Cardano_network.LeiosNotifyPipeLookahead.ResourceBounds Notification as Resources
import Cardano_network.LeiosNotifyPipeLookahead.NodeQueueBounds Notification as Queues
import Cardano_network.LeiosNotifyPipeLookahead.QueueBudget Notification as Budget
import Cardano_network.LeiosNotifyPipeLookahead.Representation Notification (offer (43 , 47) 53) as Range
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ResourceFixtures Notification as Fixture
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge exactParams ⊤ as Bridge

-- The original native paired tree uses the same successful-IO and normal-next contract.
module B = Bridge.At S.nodeNext fzero fzero hi hi
module Tree = Native.At S.nodeNext fzero fzero hi hi
open Native using (module Traces)

-- Every fresh policy history has native realization and the proved resource envelopes.
policy : ∀ {actions t} → N.Run N.initial actions t →
  (Tree.tree D.initial Traces.⟹∖√⟨ map Tree.encode (N.wireRows actions) ⟩ Tree.tree (N.driverState t)) ×
  Resources.Bounds (N.driverState t) × (Budget.total (N.queueState t) ≤ 1003)
policy trace = B.realize (P.driver trace) , Resources.initial-bounds trace , Queues.initial-total trace

-- The actual native trace can reach inFlight 1001 after a full-pipe Quit.
full-quit : Σ[ actions ∈ List N.Action ]
  (Tree.tree D.initial Traces.⟹∖√⟨ map Tree.encode (N.wireRows actions) ⟩
    Tree.tree (N.driverState (Fixture.quitFilled 1000)))
full-quit with Fixture.fresh-quit
... | actions , source = actions , B.realize (P.driver source)

-- Each finite representation maximum is exceeded by a witnessed fresh policy history.
range-obstruction : ∀ maximum → Σ[ actions ∈ List N.Action ] Σ[ t ∈ N.State ]
  ((Tree.tree D.initial Traces.⟹∖√⟨ map Tree.encode (N.wireRows actions) ⟩ Tree.tree (N.driverState t)) ×
   (Range.Fits maximum (Range.deferred (D.serverState (N.driverState t))) → ⊥))
range-obstruction maximum with Range.unbounded-deferred maximum
... | actions , t , source , exceeds = actions , t , B.realize (P.driver source) , exceeds

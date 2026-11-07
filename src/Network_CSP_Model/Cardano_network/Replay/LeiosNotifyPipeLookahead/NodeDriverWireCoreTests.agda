{-# OPTIONS --guardedness #-}

-- Wire-language normalization controls; external input truth is not inferred from logs.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverWireCoreTests where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (Notification)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBridge Notification as Reduction
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreScheduling Notification as Scheduling
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverTests as Source
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverNetworkTests as Prior
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverWireCoreNative exactParams as Native
module N = Native.At fzero fzero hi hi

-- Fresh termination with a blocked forecast is retained, including delayed Done hooks.
idle-core : Core.Run Core.initial (Node.wireRows Source.idle-actions) (Core.erase Source.idleStopped)
idle-core = Reduction.erase-run Source.idle-source

-- The fresh exact-payload Receive-before-delayed-Send witness remains admitted.
delayed-core : Core.Run Core.initial (Node.wireRows Source.delayed-actions) (Core.erase Source.delayedState)
delayed-core = Reduction.erase-run Source.delayed-source

-- Quit/Canceled drain is the same independent source wire sequence after normalization.
cancellation-core : Core.Run Core.initial (Node.wireRows Source.shutdown-actions) (Core.erase Source.shutdownState)
cancellation-core = Reduction.erase-run Source.shutdown-source

-- A normal reply selected before Quit is still allowed after its publication flag.
late-normal-core : Core.Run Core.initial (Node.wireRows Source.late-normal-actions) (Core.erase (Source.closedAt 0))
late-normal-core = Reduction.erase-run Source.late-normal-source

-- The actual client stop flag stays in the retained driver, despite erasing external snapshots.
client-stop-retained : Client.stopFlag (D.clientState (Core.driverState (Core.erase Source.shutdownState))) ≡ true
client-stop-retained = refl

-- Arbitrary final external flags do not require pretending that the original endpoints were canonical.
alternate-end : Node.State
alternate-end = Core.embed (Core.erase Source.idleStopped) true false

-- Rehydration returns a real source witness at exactly the requested noncanonical endpoint.
idle-restored-endpoint : Reduction.SourceRun Node.initial (Node.wireRows Source.idle-actions) alternate-end
idle-restored-endpoint = Reduction.core-to-source {s = Node.initial} {t = alternate-end} idle-core

-- Even an empty reduced run restores both differing external flags through actual source inputs.
empty-restored-endpoint : Reduction.SourceRun Node.initial [] (Core.embed Core.initial true true)
empty-restored-endpoint = Reduction.core-to-source {s = Node.initial} {t = Core.embed Core.initial true true} Core.stop

-- A zero-credit eligible offer is an existing source stutter, not a fabricated protocol action.
dropped-source : Node.Run Node.initial (Node.eligible Source.sample ∷ []) Node.initial
dropped-source = Node.visible (Node.applicationInput (Server.applicationOffer refl Q.dropped)) Node.stop

-- Projection removes that exact self-loop instead of creating a reduced hidden self-transition.
dropped-becomes-stop : Reduction.erase-run dropped-source ≡ Core.stop
dropped-becomes-stop = refl

-- The exact previously checked native-input cycle now projects to the empty reduced run.
forecast-cycle-becomes-stop : Reduction.erase-run Prior.forecast-cycle-source ≡ Core.stop
forecast-cycle-becomes-stop = refl

-- Positive credit still enqueues the entire supplied notification; it is not erased as a drop.
before-offer : Core.State
before-offer = Core.core D.initial (Q.credits 1 []) true

-- The target retains exact queue order/data and spends precisely one free credit.
after-offer : Core.State
after-offer = Core.core D.initial (Q.credits 0 (Source.sample ∷ [])) true

-- Productive offers remain genuine hidden transitions of the reduced wire machine.
positive-offer : Core.Tau before-offer after-offer
positive-offer = Core.offered (Node.applicationInput (Server.applicationOffer refl Q.enqueued)) (λ ())

-- Free-credit descent pays for offers without changing the existing driver potential.
offer-descends : Scheduling.rank after-offer Scheduling.≺ Scheduling.rank before-offer
offer-descends = Scheduling.decreases positive-offer

-- The original partial-state fault is retained; fresh honest-pair reachability is not asserted.
fault-end : Node.State
fault-end = Node.nodeDriver (Node.driverState Source.faultStart) Q.initial false false false

-- Normalization cannot silently delete the failed-client state while hiding its handler action.
fault-core : Core.Run (Core.erase Source.faultStart) [] (Core.erase fault-end)
fault-core = Reduction.erase-run Source.fault-source

-- Every reduced initial hidden path is accessible after flag/drop cycle elimination.
initial-accessible : Acc (λ t s → Core.Tau s t) Core.initial
initial-accessible = Scheduling.tau-accessible Core.initial

-- Accessibility also covers failed-client states while preserving possible server progress.
fault-accessible : Acc (λ t s → Core.Tau s t) (Core.erase fault-end)
fault-accessible = Scheduling.tau-accessible (Core.erase fault-end)

-- A reduced graceful trace still has an actual path of the unchanged full-policy native tree.
cancellation-native : N.B.NativeWireTrace Node.initial (Node.wireRows Source.shutdown-actions)
cancellation-native = N.core-to-native (Source.shutdownState , cancellation-core)

-- Native compatibility returns a reduced witness without deleting or sorting wire rows.
cancellation-normalized : N.CoreWire Node.initial (Node.wireRows Source.shutdown-actions)
cancellation-normalized = N.native-to-core cancellation-native

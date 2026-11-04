{-# OPTIONS --guardedness #-}

-- Concrete fresh node/native runs inhabit the universal conservation endpoints.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ConservationNativeTests where

open import Data.List using ([]; _∷_; map)
open import Data.Unit using (⊤)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤ as Native
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification ⊤ as Transport
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeConservation Notification as NodeProof
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ConservationBridge exactParams ⊤ as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverTests as Fixture

-- The existing fixtures and native conservation theorem use identical endpoint coordinates.
module Tree = Native.At S.nodeNext fzero fzero hi hi
-- The native theorem is instantiated once for all three fixture applications.
module Proof = Bridge.At S.nodeNext fzero fzero hi hi

-- Native inversion certifies the fixture whose Receive records precede both Send records.
delayed-native-accounted : Proof.Accounted (map Tree.encode (Node.wireRows Fixture.delayed-actions))
  (Tree.tree (Node.driverState Fixture.delayedState))
delayed-native-accounted = Proof.conservation Fixture.delayed-native

-- The same wire history separately has exact accounting under the restricted node policy.
delayed-node-accounted : Transport.Balanced
  (Transport.observe (Node.wireRows Fixture.delayed-actions) Transport.empty) (Node.driverState Fixture.delayedState)
delayed-node-accounted = NodeProof.transport Fixture.delayed-source

-- Canceled drain followed by Done is a nonvacuous native accounting instance.
shutdown-native-accounted : Proof.Accounted (map Tree.encode (Node.wireRows Fixture.shutdown-actions))
  (Tree.tree (Node.driverState Fixture.shutdownState))
shutdown-native-accounted = Proof.conservation Fixture.shutdown-native

-- Exact selected normal data remain accounted for after the true Quit flag.
late-normal-native-accounted : Proof.Accounted (map Tree.encode (Node.wireRows Fixture.late-normal-actions))
  (Tree.tree (Node.driverState (Fixture.closedAt 0)))
late-normal-native-accounted = Proof.conservation Fixture.late-normal-native

-- Quit remains distinct from RequestNext and is delivered exactly once in this closed pair.
shutdown-commands-settled : D.request ∷ D.quit ∷ [] ≡ D.request ∷ D.quit ∷ []
shutdown-commands-settled = NodeProof.commands-settled Fixture.shutdown-source refl refl refl

-- Done remains distinct from the Canceled reply, even when its Receive precedes Send.
shutdown-responses-settled : D.reply S.canceled ∷ D.done ∷ [] ≡ D.reply S.canceled ∷ D.done ∷ []
shutdown-responses-settled = NodeProof.responses-settled Fixture.shutdown-source refl refl refl

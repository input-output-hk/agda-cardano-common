{-# OPTIONS --safe #-}

-- All-state endpoint-preserving equivalence with the unchanged full node wire language.
module Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBridge (Notification : Set) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core

-- Original scheduling preserves its external snapshots and every retained source target.
erase-operational : ∀ {s t} → Node.Tau s t → Core.Tau (Core.erase s) (Core.erase t)
erase-operational (Node.clientSchedule {forecast = forecast} {stop = halt} proof) =
  Core.operational {forecast = forecast} {halt = halt} (Node.clientSchedule proof)
erase-operational (Node.continueReady proof) = Core.operational (Node.continueReady proof)
erase-operational (Node.terminateReady {forecast = forecast} proof) =
  Core.operational {forecast = forecast} {halt = true} (Node.terminateReady proof)
erase-operational (Node.serverSchedule {forecast = forecast} {stop = halt} proof) =
  Core.operational {forecast = forecast} {halt = halt} (Node.serverSchedule proof)
erase-operational (Node.transport {forecast = forecast} {stop = halt} proof allowed) =
  Core.operational {forecast = forecast} {halt = halt} (Node.transport proof allowed)

-- Wire record guards are independent of the two external snapshot fields.
erase-visible : ∀ {s row t} → Node.Step s (Node.wire row) t → Core.Visible (Core.erase s) row (Core.erase t)
erase-visible (Node.clientRecord actor proof) = Node.clientRecord actor proof
erase-visible (Node.serverRecord actor proof) = Node.serverRecord actor proof

-- Every original full run preserves all wire records; only actual state-stuttering inputs disappear.
erase-run : ∀ {s actions t} → Node.Run s actions t → Core.Run (Core.erase s) (Node.wireRows actions) (Core.erase t)
erase-run Node.stop = Core.stop
erase-run (Node.internal proof rest) = Core.internal (erase-operational proof) (erase-run rest)
erase-run (Node.visible proof@(Node.clientRecord _ _) rest) = Core.visible (erase-visible proof) (erase-run rest)
erase-run (Node.visible proof@(Node.serverRecord _ _) rest) = Core.visible (erase-visible proof) (erase-run rest)
erase-run (Node.visible Node.forecastInput rest) = erase-run rest
erase-run (Node.visible Node.terminateInput rest) = erase-run rest
erase-run (Node.visible (Node.applicationInput (Server.applicationOffer active Q.dropped)) rest) = erase-run rest
erase-run (Node.visible (Node.applicationInput (Server.applicationOffer active Q.enqueued)) rest) =
  Core.internal (Core.offered (Node.applicationInput (Server.applicationOffer active Q.enqueued)) (λ ())) (erase-run rest)
erase-run (Node.visible (Node.normalHandler proof) rest) = Core.internal (Core.handled (Node.normalHandler proof)) (erase-run rest)
erase-run (Node.visible (Node.canceledHandlerExit proof) rest) = Core.internal (Core.rejected (Node.canceledHandlerExit proof)) (erase-run rest)

-- Each reduced run lifts between arbitrary chosen start and end external snapshots.
lift : ∀ {s rows t} (forecast halt endForecast endHalt : Bool) → Core.Run s rows t →
  Σ[ actions ∈ List Node.Action ]
    (Node.Run (Core.embed s forecast halt) actions (Core.embed t endForecast endHalt) × Node.wireRows actions ≡ rows)
lift forecast halt endForecast endHalt Core.stop =
  Node.setForecast endForecast ∷ Node.setTerminate endHalt ∷ [] ,
  Node.visible Node.forecastInput (Node.visible Node.terminateInput Node.stop) , refl
lift forecast halt endForecast endHalt (Core.internal (Core.operational {forecast = chosenForecast} {halt = chosenHalt} proof) rest)
  with lift chosenForecast chosenHalt endForecast endHalt rest
... | actions , source , same =
  Node.setForecast chosenForecast ∷ Node.setTerminate chosenHalt ∷ actions ,
  Node.visible Node.forecastInput (Node.visible Node.terminateInput (Node.internal proof source)) , same
lift forecast halt endForecast endHalt (Core.internal (Core.offered {msg = msg} proof nonzero) rest)
  with lift false false endForecast endHalt rest
... | actions , source , same =
  Node.setForecast false ∷ Node.setTerminate false ∷ Node.eligible msg ∷ actions ,
  Node.visible Node.forecastInput (Node.visible Node.terminateInput (Node.visible proof source)) , same
lift forecast halt endForecast endHalt (Core.internal (Core.handled {msg = msg} proof) rest)
  with lift false false endForecast endHalt rest
... | actions , source , same =
  Node.setForecast false ∷ Node.setTerminate false ∷ Node.handledNormal msg ∷ actions ,
  Node.visible Node.forecastInput (Node.visible Node.terminateInput (Node.visible proof source)) , same
lift forecast halt endForecast endHalt (Core.internal (Core.rejected proof) rest)
  with lift false false endForecast endHalt rest
... | actions , source , same =
  Node.setForecast false ∷ Node.setTerminate false ∷ Node.rejectedCancel ∷ actions ,
  Node.visible Node.forecastInput (Node.visible Node.terminateInput (Node.visible proof source)) , same
lift forecast halt endForecast endHalt (Core.visible {row = row} proof rest)
  with lift false false endForecast endHalt rest
... | actions , source , same =
  Node.setForecast false ∷ Node.setTerminate false ∷ Node.wire row ∷ actions ,
  Node.visible Node.forecastInput (Node.visible Node.terminateInput (Node.visible proof source)) , cong (row ∷_) same

-- The fixed representative is a convenience instance, not a restriction on source endpoints.
canonical : ∀ {s rows t} → Core.Run s rows t →
  Σ[ actions ∈ List Node.Action ] (Node.Run (Core.canonical s) actions (Core.canonical t) × Node.wireRows actions ≡ rows)
canonical = lift false false false false

-- The independent full wire language retains actual original endpoints and every erased input witness.
SourceRun : Node.State → List D.Event → Node.State → Set
SourceRun s rows t = Σ[ actions ∈ List Node.Action ] (Node.Run s actions t × Node.wireRows actions ≡ rows)

-- Any full source witness projects to the same reduced run at its exact erased endpoints.
source-to-core : ∀ {s rows t} → SourceRun s rows t → Core.Run (Core.erase s) rows (Core.erase t)
source-to-core (actions , source , refl) = erase-run source

-- Arbitrary original flags are restored, so equivalence is not limited to canonical endpoints.
core-to-source : ∀ {s rows t} → Core.Run (Core.erase s) rows (Core.erase t) → SourceRun s rows t
core-to-source {Node.nodeDriver raw queue live forecast halt} {rows}
  {Node.nodeDriver raw′ queue′ live′ endForecast endHalt} = lift forecast halt endForecast endHalt

-- Exactly the original all-state finite wire language is preserved in both directions.
equivalence : ∀ s rows t →
  (Core.Run (Core.erase s) rows (Core.erase t) → SourceRun s rows t) ×
  (SourceRun s rows t → Core.Run (Core.erase s) rows (Core.erase t))
equivalence s rows t = core-to-source , source-to-core

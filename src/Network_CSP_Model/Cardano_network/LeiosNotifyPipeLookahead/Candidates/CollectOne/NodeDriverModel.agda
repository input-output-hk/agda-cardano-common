{-# OPTIONS --safe #-}

-- Independent CollectOne product with the unchanged production client and explicit node inputs.
-- Forecast/validation/eligibility are reported successful outcomes, not ledger proofs.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeDriverModel (Notification : Set) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; mapMaybe)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q

-- Endpoint control, transport, admission accounting and input snapshots stay distinct.
record State : Set where
  constructor nodeDriver
  field
    driverState : D.State
    queueState : Q.State
    clientAlive : Bool
    forecastReady : Bool
    terminateRequested : Bool
open State public

-- An initially blocked forecast requires an explicit readiness input before continuation.
initial : State
initial = nodeDriver D.initial Q.initial true false false

-- Replace only local client control, retaining every packet and pending record.
withClient : D.State → C.State → D.State
withClient (D.pair c s cs sc pc ps rc rs) c′ = D.pair c′ s cs sc pc ps rc rs

-- Server policy transactions update its control atomically with the separate queue.
withServer : D.State → S.State → D.State
withServer (D.pair c s cs sc pc ps rc rs) s′ = D.pair c s′ cs sc pc ps rc rs

-- The node failure flag records abnormal local driver exit, not successful wire Done.
clientView : State → Client.State
clientView (nodeDriver raw q true forecast stop) = Client.running (D.clientState raw)
clientView (nodeDriver raw q false forecast stop) = Client.unexpectedCancel (D.clientState raw)

-- The server view uses the same admission queue and peer control as the product.
serverView : State → Server.State
serverView state = Server.node (D.serverState (driverState state)) (queueState state)

-- Reuse endpoint/observation data; the candidate state and transition rules are separate.
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Alphabet
open Alphabet public using (ClientRow; ServerRow; sent; received; Action; wire;
  setForecast; setTerminate; eligible; handledNormal; rejectedCancel)

-- Source steps bind node handler policy and successful application queue transactions.
data Step : State → Action → State → Set where
  clientRecord : ∀ {raw raw′ q forecast stop row} → ClientRow row → D.Step S.nodeNext raw row raw′ →
    Step (nodeDriver raw q true forecast stop) (wire row) (nodeDriver raw′ q true forecast stop)
  serverRecord : ∀ {raw raw′ q live forecast stop row} → ServerRow row → D.Step S.nodeNext raw row raw′ →
    Step (nodeDriver raw q live forecast stop) (wire row) (nodeDriver raw′ q live forecast stop)
  forecastInput : ∀ {raw q live forecast stop ready} →
    Step (nodeDriver raw q live forecast stop) (setForecast ready) (nodeDriver raw q live ready stop)
  terminateInput : ∀ {raw q live forecast stop requested} →
    Step (nodeDriver raw q live forecast stop) (setTerminate requested) (nodeDriver raw q live forecast requested)
  applicationInput : ∀ {raw q q′ live forecast stop msg} →
    Server.Step (Server.node (D.serverState raw) q) (Server.offer msg) (Server.node (D.serverState raw) q′) →
    Step (nodeDriver raw q live forecast stop) (eligible msg) (nodeDriver raw q′ live forecast stop)
  normalHandler : ∀ {raw q forecast stop msg c′} →
    Client.Step (Client.running (D.clientState raw)) (Client.handledNormal msg) (Client.running c′) →
    Step (nodeDriver raw q true forecast stop) (handledNormal msg)
      (nodeDriver (withClient raw c′) q true forecast stop)
  canceledHandlerExit : ∀ {raw q forecast stop} →
    Client.Step (Client.running (D.clientState raw)) Client.handlerRejectedCancel
      (Client.unexpectedCancel (D.clientState raw)) →
    Step (nodeDriver raw q true forecast stop) rejectedCancel (nodeDriver raw q false forecast stop)

-- Only physical transport operations pass through the generic driver without a policy callback.
transportAllowed : ∀ {raw raw′} → Bool → D.Tau S.nodeNext raw raw′ → Bool
transportAllowed live (D.commitClient _) = live
transportAllowed live (D.decodeClient _) = live
transportAllowed _ (D.commitServer _) = true
transportAllowed _ (D.decodeServer _) = true
transportAllowed _ _ = false

-- The node's STM decision gives termination priority and gates Right 1000 on forecast readiness.
data Tau : State → State → Set where
  clientSchedule : ∀ {raw q forecast stop c′} →
    Client.Tau (Client.running (D.clientState raw)) (Client.running c′) →
    Tau (nodeDriver raw q true forecast stop) (nodeDriver (withClient raw c′) q true forecast stop)
  continueReady : ∀ {raw q c′} →
    Client.Step (Client.running (D.clientState raw)) Client.forecastAllows (Client.running c′) →
    Tau (nodeDriver raw q true true false) (nodeDriver (withClient raw c′) q true true false)
  terminateReady : ∀ {raw q forecast c′} →
    Client.Step (Client.running (D.clientState raw)) (Client.stopRequested tt) (Client.running c′) →
    Tau (nodeDriver raw q true forecast true) (nodeDriver (withClient raw c′) q true forecast true)
  serverSchedule : ∀ {raw q live forecast stop s′ q′} →
    Server.Tau (Server.node (D.serverState raw) q) (Server.node s′ q′) →
    Tau (nodeDriver raw q live forecast stop) (nodeDriver (withServer raw s′) q′ live forecast stop)
  transport : ∀ {raw raw′ q live forecast stop} (pr : D.Tau S.nodeNext raw raw′) → transportAllowed live pr ≡ true →
    Tau (nodeDriver raw q live forecast stop) (nodeDriver raw′ q live forecast stop)

-- Complete source executions retain policy inputs alongside their visible driver rows.
data Run : State → List Action → State → Set where
  stop : ∀ {s} → Run s [] s
  internal : ∀ {s t u actions} → Tau s t → Run t actions u → Run s actions u
  visible : ∀ {s t u a actions} → Step s a t → Run t actions u → Run s (a ∷ actions) u

-- The raw-driver profile erases environment/validation inputs while preserving every wire row.
wireRows : List Action → List D.Event
wireRows = mapMaybe λ { (wire row) → just row ; _ → nothing }

-- Concatenate candidate paired histories without identifying them with baseline executions.
append : ∀ {s t u actions more} → Run s actions t → Run t more u → Run s (actions ++ more) u
append stop suffix = suffix
append (internal pr run) suffix = internal pr (append run suffix)
append (visible pr run) suffix = visible pr (append run suffix)

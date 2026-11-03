{-# OPTIONS --safe #-}

-- Sound checking of supplied finite schedules; no exhaustive rejection claim.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCheck
  (Notification : Set) (notificationEq : DecidableEquality Notification) where

open import Data.Bool using (true; false)
import Data.Bool.Properties as Bool
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Notification ⊤ notificationEq as CE
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification ⊤ notificationEq as DE
open import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification
open import Cardano_network.LeiosNotifyPipeLookahead.Selection using (select)
module SX = S.Executable notificationEq

-- Schedule data name permitted operations without supplying their proof evidence.
data Choice : Set where
  client server : ℕ → Choice
  accept excessive queued continue terminate : Choice
  transport : DE.Choice → Choice

-- Supplied instructions retain every visible policy input and wire record.
data Instruction : Set where
  hidden : Choice → Instruction
  action : Action → Instruction

-- Internal interpretation reconstructs the independent node transition certificate.
hidden-step : (s : State) → Choice → Maybe (Σ[ t ∈ State ] Tau s t)
hidden-step (nodeDriver raw@(D.pair c s cs sc pc ps rc rs) q true forecast halt) (client n)
  with select (CE.internalMoves c) n
... | nothing = nothing
... | just (c′ , pr) = just (_ , clientSchedule (Client.schedule pr))
hidden-step (nodeDriver raw@(D.pair c s cs sc pc ps rc rs) q live forecast halt) (server n)
  with select (S.internalMoves s) n
... | nothing = nothing
... | just (s′ , pr) with Server.routine pr Bool.≟ true
...   | no _ = nothing
...   | yes allowed = just (_ , serverSchedule (Server.schedule pr allowed))
hidden-step (nodeDriver (D.pair c (S.state S.admit w sender completed flag) cs sc pc ps rc rs)
    (Q.credits free messages) live forecast halt) accept with free Nat.≟ 1000
... | yes _ = nothing
... | no unequal = just (_ , serverSchedule (Server.admitAccepted (Q.admitted unequal)))
hidden-step (nodeDriver (D.pair c (S.state S.admit w sender completed flag) cs sc pc ps rc rs)
    (Q.credits free messages) live forecast halt) excessive with free Nat.≟ 1000
... | no _ = nothing
... | yes equal = just (_ , serverSchedule (Server.admitExcessive (Q.excessive equal)))
hidden-step (nodeDriver (D.pair c s cs sc pc ps rc rs) (Q.credits free (msg ∷ messages)) live forecast halt) queued
  with SX.lookup S.nodeNext s (S.nextReply (S.normal msg))
... | nothing = nothing
... | just (s′ , pr) = just (_ , serverSchedule (Server.nextQueued Q.dequeued pr))
hidden-step (nodeDriver (D.pair c s cs sc pc ps rc rs) q true true false) continue
  with CE.lookup (C.continue (+ 1000)) c
... | nothing = nothing
... | just (c′ , pr) = just (_ , continueReady (Client.continueAtDepth pr))
hidden-step (nodeDriver (D.pair c s cs sc pc ps rc rs) q true forecast true) terminate
  with CE.lookup (C.terminate tt) c
... | nothing = nothing
... | just (c′ , pr) = just (_ , terminateReady (Client.terminate pr))
hidden-step (nodeDriver raw q live forecast halt) (transport choice)
  with DE.hidden S.nodeNext raw choice
... | nothing = nothing
... | just (raw′ , pr) with transportAllowed live pr Bool.≟ true
...   | no _ = nothing
...   | yes allowed = just (_ , Tau.transport pr allowed)
hidden-step _ _ = nothing

-- Visible interpretation checks exact wire packets, environment inputs and normal handlers.
visible-step : (s : State) (a : Action) → Maybe (Σ[ t ∈ State ] Step s a t)
visible-step (nodeDriver raw q true forecast halt) (wire row@(D.clientSend _)) with DE.lookup S.nodeNext row raw
... | nothing = nothing
... | just (raw′ , pr) = just (_ , clientRecord sent pr)
visible-step (nodeDriver raw q true forecast halt) (wire row@(D.clientRecv _)) with DE.lookup S.nodeNext row raw
... | nothing = nothing
... | just (raw′ , pr) = just (_ , clientRecord received pr)
visible-step (nodeDriver raw q live forecast halt) (wire row@(D.serverSend _)) with DE.lookup S.nodeNext row raw
... | nothing = nothing
... | just (raw′ , pr) = just (_ , serverRecord sent pr)
visible-step (nodeDriver raw q live forecast halt) (wire row@(D.serverRecv _)) with DE.lookup S.nodeNext row raw
... | nothing = nothing
... | just (raw′ , pr) = just (_ , serverRecord received pr)
visible-step (nodeDriver raw q live forecast halt) (setForecast ready) = just (_ , forecastInput)
visible-step (nodeDriver raw q live forecast halt) (setTerminate requested) = just (_ , terminateInput)
visible-step (nodeDriver raw (Q.credits free messages) live forecast halt) (eligible msg)
  with S.active (S.reader (D.serverState raw)) Bool.≟ true
... | no _ = nothing
... | yes active with free
...   | zero = just (_ , applicationInput (Server.applicationOffer active Q.dropped))
...   | suc n = just (_ , applicationInput (Server.applicationOffer active Q.enqueued))
visible-step (nodeDriver (D.pair c s cs sc pc ps rc rs) q true forecast halt) (handledNormal msg)
  with CE.lookup (C.handled (S.normal msg)) c
... | nothing = nothing
... | just (c′ , pr) = just (_ , normalHandler (Client.handled pr))
visible-step _ _ = nothing

-- Erasure removes only supplied hidden instructions; no visible record is dropped.
actions : List Instruction → List Action
actions [] = []
actions (hidden _ ∷ instructions) = actions instructions
actions (action a ∷ instructions) = a ∷ actions instructions

-- Evaluation checks each supplied instruction rather than searching for a schedule.
evaluate : State → List Instruction → Maybe State
evaluate s [] = just s
evaluate s (hidden choice ∷ instructions) with hidden-step s choice
... | nothing = nothing
... | just (t , _) = evaluate t instructions
evaluate s (action a ∷ instructions) with visible-step s a
... | nothing = nothing
... | just (t , _) = evaluate t instructions

-- Successful evaluation yields the original independent node Run at exactly its actions.
sound : ∀ {s instructions t} → evaluate s instructions ≡ just t → Run s (actions instructions) t
sound {instructions = []} equal with just-injective equal
... | refl = Run.stop
sound {s} {hidden choice ∷ instructions} equal with hidden-step s choice
... | nothing with equal
...   | ()
sound {s} {hidden choice ∷ instructions} equal | just (t , pr) =
  Run.internal pr (sound {s = t} {instructions = instructions} equal)
sound {s} {action a ∷ instructions} equal with visible-step s a
... | nothing with equal
...   | ()
sound {s} {action a ∷ instructions} equal | just (t , pr) =
  Run.visible pr (sound {s = t} {instructions = instructions} equal)

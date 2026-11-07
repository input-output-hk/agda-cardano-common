{-# OPTIONS --safe #-}

-- Sound checking of supplied finite schedules; no exhaustive rejection claim.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCheck
  (Notification : Set) (notificationEq : DecidableEquality Notification) where

open import Data.Bool using (true; false)
import Data.Bool.Properties as Bool
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
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

-- Protocol selectors are shared with the full node operational tree.
open import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverExecution Notification notificationEq public using
  (Choice; client; server; accept; excessive; queued; continue; terminate; transport; hidden-step; visible-step; visible-complete; hidden-complete)

-- Supplied instructions retain every visible policy input and wire record.
data Instruction : Set where
  hidden : Choice → Instruction
  action : Action → Instruction

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

-- A chosen hidden target prefixes an existing successful supplied-instruction evaluation.
evaluate-hidden : ∀ {s middle target choice instructions} →
  map proj₁ (hidden-step s choice) ≡ just middle → evaluate middle instructions ≡ just target →
  evaluate s (hidden choice ∷ instructions) ≡ just target
evaluate-hidden {s} {choice = choice} chosen finished with hidden-step s choice | chosen
... | just (_ , _) | refl = finished

-- The corresponding visible instruction retains its exact source action and target.
evaluate-action : ∀ {s middle target a instructions} →
  map proj₁ (visible-step s a) ≡ just middle → evaluate middle instructions ≡ just target →
  evaluate s (action a ∷ instructions) ≡ just target
evaluate-action {s} {a = a} chosen finished with visible-step s a | chosen
... | just (_ , _) | refl = finished

-- Every finite full-policy run has supplied instructions preserving all original actions and its target.
complete : ∀ {s sourceActions target} → Run s sourceActions target →
  Σ[ instructions ∈ List Instruction ] (actions instructions ≡ sourceActions × evaluate s instructions ≡ just target)
complete Run.stop = [] , refl , refl
complete {s = s} {target = target} (Run.internal {t = middle} step rest) with hidden-complete step | complete rest
... | choice , chosen | instructions , same , finished =
  hidden choice ∷ instructions , same ,
  evaluate-hidden {s = s} {middle = middle} {target = target} {choice = choice} {instructions = instructions} chosen finished
complete {s = s} {target = target} (Run.visible {t = middle} {a = a} step rest) with complete rest
... | instructions , same , finished =
  action a ∷ instructions , cong (a ∷_) same ,
  evaluate-action {s = s} {middle = middle} {target = target} {a = a} {instructions = instructions} (visible-complete step) finished

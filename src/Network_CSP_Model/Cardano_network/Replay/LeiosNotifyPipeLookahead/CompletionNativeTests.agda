{-# OPTIONS --guardedness #-}

-- Arbitrarily long occupancy-one production histories and exact native shutdown work.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CompletionNativeTests where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤ as Native
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Projection
import Cardano_network.LeiosNotifyPipeLookahead.CompletionDriver Notification ⊤ as Count
import Cardano_network.LeiosNotifyPipeLookahead.SequentialCompletion
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CompletionBridge exactParams ⊤ as Bridge

-- The exact-field notification is supplied under the node model's existing eligibility contract.
sample : Notification
sample = offer (43 , 47) 53

-- The production-policy family keeps its actual fixed depth, credits and handler behavior.
module Family = Cardano_network.LeiosNotifyPipeLookahead.SequentialCompletion Notification sample

-- Native endpoint coordinates and production callback contract match earlier exact fixtures.
module Proof = Bridge.At S.nodeNext fzero fzero hi hi
open Native using (module Traces)

-- Every finite number of occupancy-one rounds is reachable in the actual native paired tree.
prefix-native : ∀ n → Proof.Tree.tree D.initial Traces.⟹∖√⟨ map Proof.Tree.encode
  (Node.wireRows ((Node.setForecast true ∷ []) ++ Family.history n)) ⟩
  Proof.Tree.tree (Node.driverState (Family.ready (Family.reader n) n))
prefix-native n = Proof.B.realize (Projection.driver (Family.prefix n))

-- Shutdown's original wire word contains Quit and Done without any new request record.
quit-rows : List D.Event
quit-rows = D.clientSend D.quit ∷ D.serverRecv D.quit ∷ D.serverSend D.done ∷ D.clientRecv D.done ∷ []

-- The arbitrary-length token drain has an actual native continuation at those same endpoints.
shutdown-native : ∀ n → Proof.Tree.tree (Node.driverState (Family.ready (Family.reader n) n))
  Traces.⟹∖√⟨ map Proof.Tree.encode quit-rows ⟩ Proof.Tree.tree (Node.driverState Family.closed)
shutdown-native n = Proof.B.realize (Projection.driver (Family.shutdown (Family.reading n) n))

-- Exact native encoding leaves only the original source row as a possible decoded match.
canonical-rows : ∀ rows {other} → Proof.B.Matches (map Proof.Tree.encode rows) other → other ≡ rows
canonical-rows [] Proof.B.empty = refl
canonical-rows (row ∷ rows) (Proof.B.matched decoded matching)
  with just-injective (trans (sym decoded) (Proof.B.Canonical.decode-encode row))
... | refl = cong (row ∷_) (canonical-rows rows matching)

-- The independent native analysis recovers the exact four original shutdown records.
decoded-shutdown-rows : ∀ n → Proof.rows (Proof.analyze (shutdown-native n)) ≡ quit-rows
decoded-shutdown-rows n = canonical-rows quit-rows (Proof.matching (Proof.analyze (shutdown-native n)))

-- The actual server Send-Done certifies reconstructed server closure without tree injectivity.
analyzed-closed : ∀ n → D.serverState (Proof.target (Proof.analyze (shutdown-native n))) ≡
  S.state S.closed 0 S.idle 0 true
analyzed-closed n = Proof.seen-done (shutdown-native n)
  (subst (Any (λ row → row ≡ D.serverSend D.done)) (sym (decoded-shutdown-rows n)) (there (there (here refl))))

-- Counting actual native hidden flushes gives exactly the unbounded accumulated completion history.
native-flushes : ∀ n → Proof.flushes (shutdown-native n) ≡ n
native-flushes n = trans (Proof.closed-flushes (shutdown-native n) (analyzed-closed n))
  (trans (cong (Count.work (Node.driverState (Family.ready (Family.reader n) n)) +_)
      (cong Count.requests (decoded-shutdown-rows n)))
    (trans (+-identityʳ (Count.work (Node.driverState (Family.ready (Family.reader n) n))))
      (Family.ready-work (Family.reading n) n)))

-- Every such native close has at least n actual hidden-plus-wire operations.
native-lower-bound : ∀ n → n ≤ Proof.Operations.steps (shutdown-native n)
native-lower-bound n = Proof.completed-lower-bound (shutdown-native n) (analyzed-closed n)

-- The selected actual native shutdown family has the stronger exact count n plus twelve.
native-steps : ∀ n → Proof.Operations.steps (shutdown-native n) ≡ n + 12
native-steps n = trans (Proof.realize-steps (Projection.driver (Family.shutdown (Family.reading n) n)))
  (Family.shutdown-steps (Family.reading n) n)

-- Natural occupancy bounds remain certified at every state of the producing policy prefix.
native-prefix-resources : ∀ n → Family.AllBounds (Family.prefix n)
native-prefix-resources = Family.prefix-bounds

-- The whole production policy history and shutdown have native realization, not only a local server run.
full-native : ∀ n → Proof.Tree.tree D.initial Traces.⟹∖√⟨ map Proof.Tree.encode
  (Node.wireRows (((Node.setForecast true ∷ []) ++ Family.history n) ++ Family.shutdown-actions)) ⟩
  Proof.Tree.tree (Node.driverState Family.closed)
full-native n = Proof.B.realize (Projection.driver (Family.full n))

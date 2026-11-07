{-# OPTIONS --guardedness #-}

-- Actual fresh node runs exercise unobserved offers, exact observations and inventory scope.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeBasisAdequacyTests where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
  using (Notification; notificationEq; votes)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBridge Notification as Reduction
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBasis Notification as Basis
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeBasisAdequacy Notification as Adequacy
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverTests as Source

-- An actual notification is supplied explicitly as the unobserved-choice representative.
fallback : Notification
fallback = votes []

-- EOF can leave a real eligible notification queued before any normal wire hook exists.
hidden-actions : List Node.Action
hidden-actions = Node.setForecast true ∷ Node.wire (D.serverRecv D.request) ∷ Node.eligible Source.sample ∷ []

-- Exact protocol fields include the still pending RequestNext Send record and queue contents.
hidden-target : Node.State
hidden-target = Node.nodeDriver
  (D.pair (C.client C.writingRequest C.awaiting [] [] 0 (+ 0) false nothing)
    (S.state S.awaitNext 1 S.idle 0 false) [] [] (just D.request) nothing nothing nothing)
  (Q.credits 0 (Source.sample ∷ [])) true true false

-- This is a fresh full-policy witness, not a synthetic arbitrary initial queued store.
hidden-source : Node.Run Node.initial hidden-actions hidden-target
hidden-source =
  Node.visible Node.forecastInput $
  Node.internal (Node.continueReady (Client.continueAtDepth C.continueZero)) $
  Node.internal (Node.clientSchedule (Client.schedule C.registerResponse)) $
  Node.internal (Node.clientSchedule (Client.schedule (C.startResponse refl))) $
  Node.internal (Node.transport (D.commitClient C.sentRequest) refl) $
  Node.internal (Node.transport (D.decodeServer (S.receiveRequest S.atFirst)) refl) $
  Node.visible (Node.serverRecord Node.received (D.serverReceived (S.receiveRequest S.atFirst))) $
  Node.internal (Node.serverSchedule (Server.admitAccepted (Q.admitted (λ ())))) $
  Node.internal (Node.serverSchedule (Server.schedule S.registered refl)) $
  Node.visible (Node.applicationInput (Server.applicationOffer refl Q.enqueued)) Node.stop

-- The sole logged row has no normal payload; every actual wire occurrence remains present.
hidden-rows : List D.Event
hidden-rows = Node.wireRows hidden-actions

module Hidden = Adequacy.ForInput notificationEq fallback hidden-rows

-- Only the explicitly supplied fallback is required when every normal choice is still unobserved.
hidden-basis : Hidden.basis ≡ fallback ∷ []
hidden-basis = refl

-- The unobserved source offer is replaced without changing any logged field.
unobserved-mapped : Hidden.retract Source.sample ≡ fallback
unobserved-mapped = refl

-- Exact queued count and order survive, with only its unobserved value renamed.
hidden-queue : Q.queued (Core.queueState (Hidden.M.coreState (Core.erase hidden-target))) ≡ fallback ∷ []
hidden-queue = refl

-- Adequacy constructs an actual restricted run with that mapped endpoint and unchanged wire prefix.
hidden-restricted : Hidden.B.Run Core.initial hidden-rows (Hidden.M.coreState (Core.erase hidden-target))
hidden-restricted = Hidden.adequate (Reduction.erase-run hidden-source)

-- Removing basis evidence still yields a full original-node witness for the identical wire prefix.
hidden-full-node : Hidden.NodeSourceTrace hidden-rows
hidden-full-node = Hidden.basis→node (Hidden.M.coreState (Core.erase hidden-target) , hidden-restricted)

-- Separate endpoint fragments provide an inventory, not an invented global timestamp ordering.
client-fragment : List D.Event
client-fragment = D.clientRecv (D.reply (S.normal Source.sample)) ∷ D.clientSend D.request ∷ []

-- The source server fragment keeps its own RequestNext/normal reply order.
server-fragment : List D.Event
server-fragment = D.serverRecv D.request ∷ D.serverSend (D.reply (S.normal Source.sample)) ∷ []

module Merged = Adequacy.ForInput notificationEq fallback (client-fragment ++ server-fragment)

-- This actual fresh merge is different from the concatenation used only as payload inventory.
merge-covered : ∀ {row} → row ∈ Node.wireRows Source.delayed-actions → row ∈ client-fragment ++ server-fragment
merge-covered (here refl) = there (there (here refl))
merge-covered (there (here refl)) = here refl
merge-covered (there (there (here refl))) = there (here refl)
merge-covered (there (there (there (here refl)))) = there (there (there (here refl)))
merge-covered (there (there (there (there ()))))

-- Every compatible merge can reuse the same complete endpoint inventory.
merged-restricted : Merged.B.Run Core.initial (Node.wireRows Source.delayed-actions)
  (Merged.M.coreState (Core.erase Source.delayedState))
merged-restricted = Merged.adequate-covered merge-covered (Reduction.erase-run Source.delayed-source)

-- An observed payload remains exact even in the receiver's final unhandled state.
observed-target-fixed : Merged.M.coreState (Core.erase Source.delayedState) ≡ Core.erase Source.delayedState
observed-target-fixed = refl

-- This counterexample to unrestricted nonfresh fixing is a qualified partial-state inventory control.
partial-store : Core.State
partial-store = Core.core D.initial (Q.credits 0 (Source.sample ∷ [])) true

-- A payload absent from the inventory is genuinely changed, so the fixed-start premise cannot be assumed.
uncovered-store-not-fixed : Hidden.M.coreState partial-store ≡ partial-store → ⊥
uncovered-store-not-fixed ()

-- Including that known payload in the explicit inventory makes this actual initial-state premise inhabited.
covered-store-fixed : Merged.M.coreState partial-store ≡ partial-store
covered-store-fixed = refl

-- The all-state theorem is usable with a proved fixed initial store; no fresh reachability is asserted.
nonfresh-restricted : Merged.B.Run partial-store [] partial-store
nonfresh-restricted = Merged.adequate-from covered-store-fixed (λ ()) Core.stop

-- An ordered duplicate-vote payload is one whole normal value, never a set of inner votes.
duplicate-votes : Notification
duplicate-votes = votes ((1 , 2) ∷ (3 , 4) ∷ (1 , 2) ∷ [])

-- These schema-level repeated observations test retention, not protocol acceptance of this standalone word.
repeated : List D.Event
repeated = D.serverSend (D.reply (S.normal duplicate-votes)) ∷
  D.clientRecv (D.reply (S.normal duplicate-votes)) ∷
  D.serverSend (D.reply (S.normal duplicate-votes)) ∷ []

module Observed = Adequacy.ForInput notificationEq fallback repeated

-- Candidate enumeration deduplication never removes observed wire occurrences or inner vote duplicates.
unique-candidates : Observed.basis ≡ fallback ∷ duplicate-votes ∷ []
unique-candidates = refl

-- The standard-library uniqueness proof remains the same reused basis certificate.
unique-certificate : Unique Observed.basis
unique-certificate = Observed.duplicate-free

-- The full opaque payload, including ordered repeated votes, is fixed by retraction.
votes-fixed : Observed.retract duplicate-votes ≡ duplicate-votes
votes-fixed = refl

-- Every supplied repeated row survives, in place and with its original exact payload.
repeated-fixed : map Observed.M.Driver.event repeated ≡ repeated
repeated-fixed = Observed.rows-fixed repeated (λ present → present)

-- All three visible occurrences remain even though the candidate alphabet has only two values.
repeated-count : length (map Observed.M.Driver.event repeated) ≡ 3
repeated-count = refl

module Empty = Basis []

-- Cancellation remains a control fault even when no eligible payload can be supplied.
fault-target : Core.State
fault-target = Core.erase (Node.nodeDriver (Node.driverState Source.faultStart) Q.initial false false false)

-- This is the existing qualified partial-state fault, with no fresh honest-pair reachability assertion.
cancel-fault-unrestricted : Core.Tau (Core.erase Source.faultStart) fault-target
cancel-fault-unrestricted = Core.rejected (Node.canceledHandlerExit (Client.rejectedCancel refl refl))

-- Restricting eligible offers cannot accidentally remove the Cancel fault branch.
cancel-fault-empty-basis : Empty.Tau (Core.erase Source.faultStart) fault-target
cancel-fault-empty-basis = cancel-fault-unrestricted , tt

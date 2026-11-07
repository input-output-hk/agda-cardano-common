{-# OPTIONS --safe #-}

-- Executable selectors retain the existing node-client rules and failure state.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.LeiosNotifyPipeLookahead.NodeClientExecution
  (Notification Return : Set) (notificationEq : DecidableEquality Notification) where

open import Data.Bool using (true)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Notification Return notificationEq as CE
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification Return as N

-- A successful guard keeps the independently specified exact target and proof.
checked : ∀ {s a t} {P : Set} → Dec P → (P → N.Step s a t) →
  Maybe (Σ[ u ∈ N.State ] N.Step s a u)
checked {t = t} (yes proof) build = just (t , build proof)
checked (no _) _ = nothing

-- Erasing a successful guard certificate does not depend on its proof identity.
checked-target : ∀ {s a t} {P : Set} (decision : Dec P) {build : P → N.Step s a t} →
  P → Maybe.map proj₁ (checked decision build) ≡ just t
checked-target (yes _) _ = refl
checked-target (no absent) proof = ⊥-elim (absent proof)

-- Lift a certified generic operation only through the caller's actual node rule.
lift : ∀ {c operation action} →
  (∀ {target} → C.Step c operation target → N.Step (N.running c) action (N.running target)) →
  Maybe (Σ[ target ∈ C.State ] C.Step c operation target) →
  Maybe (Σ[ target ∈ N.State ] N.Step (N.running c) action target)
lift build (just (target , proof)) = just (N.running target , build proof)
lift _ nothing = nothing

-- The whitelist prevents local decisions from being supplied as wire records.
lookup : (action : N.Action) (s : N.State) → Maybe (Σ[ target ∈ N.State ] N.Step s action target)
lookup _ (N.unexpectedCancel _) = nothing
lookup (N.wire C.sendRequest) (N.running c) = lift (N.wireRecord N.request) (CE.lookup C.sendRequest c)
lookup (N.wire C.sendQuit) (N.running c) = lift (N.wireRecord N.quit) (CE.lookup C.sendQuit c)
lookup (N.wire (C.recvReply reply)) (N.running c) = lift (N.wireRecord N.reply) (CE.lookup (C.recvReply reply) c)
lookup (N.wire C.recvDone) (N.running c) = lift (N.wireRecord N.done) (CE.lookup C.recvDone c)
lookup N.forecastAllows (N.running c) = lift N.continueAtDepth (CE.lookup (C.continue (+ 1000)) c)
lookup (N.stopRequested value) (N.running c) = lift N.terminate (CE.lookup (C.terminate value) c)
lookup (N.handledNormal value) (N.running c) = lift N.handled (CE.lookup (C.handled (S.normal value)) c)
lookup N.handlerRejectedCancel (N.running (C.client m (C.handling S.canceled) js rs n a q v)) =
  checked (C.active m Bool.≟ true) (λ active → N.rejectedCancel active refl)
lookup _ _ = nothing

-- Public state execution drops the certificate after certified rule selection.
next : N.State → N.Action → Maybe N.State
next s action = Maybe.map proj₁ (lookup action s)

-- Every independent node rule has exactly the target returned by execution.
next-complete : ∀ {s action target} → N.Step s action target → next s action ≡ just target
next-complete (N.wireRecord {c = c} N.request proof)
  with CE.lookup C.sendRequest c | CE.next-complete proof
... | just (_ , _) | refl = refl
next-complete (N.wireRecord {c = c} N.quit proof)
  with CE.lookup C.sendQuit c | CE.next-complete proof
... | just (_ , _) | refl = refl
next-complete (N.wireRecord {c = c} (N.reply {m = reply}) proof)
  with CE.lookup (C.recvReply reply) c | CE.next-complete proof
... | just (_ , _) | refl = refl
next-complete (N.wireRecord {c = c} N.done proof)
  with CE.lookup C.recvDone c | CE.next-complete proof
... | just (_ , _) | refl = refl
next-complete (N.continueAtDepth {c = c} proof)
  with CE.lookup (C.continue (+ 1000)) c | CE.next-complete proof
... | just (_ , _) | refl = refl
next-complete (N.terminate {c = c} {x = value} proof)
  with CE.lookup (C.terminate value) c | CE.next-complete proof
... | just (_ , _) | refl = refl
next-complete (N.handled {c = c} {m = value} proof)
  with CE.lookup (C.handled (S.normal value)) c | CE.next-complete proof
... | just (_ , _) | refl = refl
next-complete (N.rejectedCancel {c = C.client m _ js rs n a q v} active refl) =
  checked-target (C.active m Bool.≟ true) active

-- Internal moves retain their actual node scheduling rule, excluding callbacks.
Internal : N.State → Set
Internal s = Σ[ target ∈ N.State ] N.Tau s target

-- Generic bookkeeping is inherited only while the local driver is running.
liftInternal : ∀ {c} → CE.Internal c → Internal (N.running c)
liftInternal (target , proof) = N.running target , N.schedule proof

-- The generic menu preserves both main-thread and receiver scheduling choices.
internalMoves : (s : N.State) → List (Internal s)
internalMoves (N.running c) = map liftInternal (CE.internalMoves c)
internalMoves (N.unexpectedCancel _) = []

-- State-only scheduling targets erase proofs after constructing the finite menu.
targets : N.State → List N.State
targets s = map proj₁ (internalMoves s)

-- Every listed hidden scheduling target is independently permitted by NodeClientModel.
target-sound : ∀ {s target} → target ∈ targets s → N.Tau s target
target-sound member with ∈-map⁻ proj₁ member
... | (_ , proof) , _ , refl = proof

-- Every existing node scheduling rule is included, without a reachable-state premise.
target-complete : ∀ {s target} → N.Tau s target → target ∈ targets s
target-complete (N.schedule proof) with ∈-map⁻ proj₁ (CE.target-complete proof)
... | (_ , _) , member , refl = ∈-map⁺ proj₁ (∈-map⁺ liftInternal member)

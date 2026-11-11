{-# OPTIONS --guardedness #-}

-- Inner Async scope transitions change no caller, monitor or body handle.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesScopes
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesContext as ContextFacts
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module V = ContextFacts isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- Supply arbitrary scope metadata while keeping every ownership observation.
scope-write : ∀ s next → D.Held s → D.Held (record s { scopes = next })
scope-write s next (inv , unique , aux) =
  V.copy-inv (PS.cm s) (C.capture s) (C.capture (record s { scopes = next })) inv , unique ,
  V.copy-aux (C.capture s) (C.capture (record s { scopes = next })) aux

-- Every actual scope constructor mirrors its own dispatcher with-tree.
scope-step : ∀ a s {t} → PS.step (PS.scope a) s ≡ just t → D.Held s → D.Held t
scope-step Scope.deliverCancel s eq held with Scope.cursor (PS.scopes s) | GP.Pool.parentFork (GP.pool (PS.governor s))
... | Scope.closing Scope.governor | just j = case eq of λ ()
scope-step Scope.deliverCancel s eq held | Scope.closing Scope.governor | nothing with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.deliverCancel s eq held | Scope.openScope | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.deliverCancel s eq held | Scope.readyToFinish | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.deliverCancel s eq held | Scope.finishedScope | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.deliverCancel s eq held | Scope.closing Scope.churn | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.deliverCancel s eq held | Scope.closing Scope.localRoot | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.deliverCancel s eq held | Scope.closing Scope.ledger | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.beginUnwind s eq held with Scope.step (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.requestCancel s eq held with Scope.step (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.join s eq held with Scope.step (PS.governorPoolClosed s) Scope.join (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step Scope.finishClose s eq held with Scope.step (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step (Scope.bodyExit actor) s eq held with Scope.step (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step (Scope.publishResult actor) s eq held with Scope.step (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }
scope-step (Scope.beginFailure actor) s eq held with Scope.step (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → scope-write s next held }

-- The shared K wrapper keeps its real peerOpen permission.
k-scope-step : ∀ a s {t} → K.step (K.peerStep (PS.scope a)) s ≡ just t → R.Reach s → R.Reach t
k-scope-step a s stepped held with K.peerOpen s ∧ K.peerAllowed (PS.scope a) s
... | false = case stepped of λ ()
... | true with PS.step (PS.scope a) (K.peers s) in advanced
...   | nothing = case stepped of λ ()
...   | just p = case just-injective stepped of λ { refl → scope-step a (K.peers s) advanced held }

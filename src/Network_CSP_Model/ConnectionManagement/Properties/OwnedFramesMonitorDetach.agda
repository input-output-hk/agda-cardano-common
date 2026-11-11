{-# OPTIONS --guardedness #-}

-- Monitor exceptions and cancellation detach the caller before changing its
-- physical observer PC/handle, so no remaining frame loses an exact owner.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesMonitorDetach
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.OwnedFramesStores using (delete-self)
open import ConnectionManagement.Properties.OutboundKeys using (acquireFrames; releaseFrames)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesCancel as CancelFacts
import ConnectionManagement.Properties.OwnedFramesUniquePeers as UniqueFacts
import ConnectionManagement.Properties.OwnedFramesFollowDelete as DeleteFacts
import ConnectionManagement.Properties.OwnedFramesThreadUpdate as ThreadFacts
import ConnectionManagement.Properties.OwnedFramesMonitorLifecycle as Lifecycle
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module X = Auxiliary isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module U = UniqueFacts isIOManagerError
  module F = DeleteFacts isBearerClosed isIOManagerError
  module T = ThreadFacts isBearerClosed isIOManagerError
  module M = Lifecycle isBearerClosed isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- Detach retains physical metadata and leaves no logical followup at this peer.
DetachFacts : PS.State → PS.Thread → PS.State → Set
DetachFacts s observer next = D.Held next × PS.monitors next ≡ PS.monitors s ×
  PS.monitorPool next ≡ PS.monitorPool s × lookup (PS.peerRef observer) (Sub.monitors (PS.machine next)) ≡ nothing

-- Both successful detach branches use the real cancellation start and the
-- unique logical followup table; no observer/handle is prematurely removed.
detach : ∀ err observer s {f next} → PS.detach err observer s ≡ just (f , next) → D.Held s → DetachFacts s observer next
detach err observer s eq (inv , unique , aux) with lookup (PS.worker observer) (O.acquiring (PS.cm s))
... | just active = case eq of λ ()
... | nothing with lookup (PS.peerRef observer) (Sub.monitors (PS.machine s)) in absent
...   | nothing with Cancel.start (PS.worker observer) err Cancel.ordinary (PS.cm s) in started
...     | nothing = case eq of λ ()
...     | just (f , c′) = case just-injective eq of λ { refl →
  (D.start-inv (PS.worker observer) err Cancel.ordinary (PS.cm s) started (C.capture s) unique inv ,
   U.start-unique (PS.worker observer) err Cancel.ordinary (PS.cm s) started unique , aux) , refl , refl , absent }
detach err observer s eq (inv , unique , aux) | nothing | just follow with J.caller follow ≟ PS.worker observer
... | no apart = case eq of λ ()
... | yes caller with Cancel.start (PS.worker observer) err Cancel.ordinary (PS.cm s) in started
...   | nothing = case eq of λ ()
...   | just (f , c′) = case just-injective eq of λ { refl →
  (F.detach-inv c′ (C.capture s) (PS.peerRef observer) follow (PS.worker observer) absent caller
    (proj₁ (proj₂ cleared)) (proj₂ (proj₂ cleared))
    (D.start-inv (PS.worker observer) err Cancel.ordinary (PS.cm s) started (C.capture s) unique inv) ,
   U.start-unique (PS.worker observer) err Cancel.ordinary (PS.cm s) started unique , F.delete-aux (C.capture s) (PS.peerRef observer) aux) ,
  refl , refl , delete-self (PS.peerRef observer) (Sub.monitors (PS.machine s)) (X.Aux.followKeys aux) }
  where cleared = CancelFacts.start-clears (PS.worker observer) err Cancel.ordinary (PS.cm s) started (acquireFrames unique) (releaseFrames unique)

-- Synchronous monitor error runs on the already-detached source/context.
monitor-exception : ∀ tid err s {t} → PS.step (PS.monitorException tid err) s ≡ just t → D.Held s → D.Held t
monitor-exception tid err s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just observer with PS.bodyActive tid observer s | PS.detach err observer s in detached
...   | true | just (f , next) = case just-injective eq of λ { refl → M.thread-write next tid observer next-thread (PS.monitorPool next)
  saved′ refl refl (λ uid apart → refl)
  (T.keep-detached (C.capture next) tid observer next-thread (PS.monitorPool next) (X.Aux.monitorKeys (proj₂ (proj₂ next-held))) saved′ missing) next-held }
  where
  facts = detach err observer s detached held
  next-held = proj₁ facts
  saved′ = trans (cong (lookup tid) (proj₁ (proj₂ facts))) saved
  missing = proj₂ (proj₂ (proj₂ facts))
  next-thread = record observer { pc = PS.errorWait err; interrupted = just f; followup = lookup (PS.peerRef observer) (Sub.monitors (PS.machine s)) }
monitor-exception tid err s eq held | just observer | false | result = case eq of λ ()
monitor-exception tid err s eq held | just observer | true | nothing = case eq of λ ()

-- The selected monitor cancellation writes exactly its one physical handle.
cancel-handles : ∀ p tid {p′} → PS.Pool.phase p ≡ PS.Pool.cancelPending tid →
  PS.Pool.step PS.Pool.deliverCancel p ≡ just p′ → PS.Pool.handles p′ ≡ put tid PS.Pool.bodyUnwinding (PS.Pool.handles p)
cancel-handles p tid phase eq rewrite phase with lookup tid (PS.Pool.handles p)
... | just PS.Pool.bodyRunning = case just-injective eq of λ { refl → refl }
... | nothing = case eq of λ ()
... | just PS.Pool.bodyUnwinding = case eq of λ ()
... | just (PS.Pool.bodyReturned _) = case eq of λ ()
... | just (PS.Pool.deregisterPending _) = case eq of λ ()
... | just (PS.Pool.deregistered _) = case eq of λ ()
... | just (PS.Pool.resultAvailable _) = case eq of λ ()

-- Ordinary and blocked handler delivery share detachment; the input Bool keeps
-- the original monitorDeliverable masking gate unchanged.
deliver-monitor : ∀ blocked err s {t} → PS.deliverMonitor blocked err s ≡ just t → D.Held s → D.Held t
deliver-monitor blocked err s eq held with PS.Pool.phase (PS.monitorPool s) in phase
... | PS.Pool.cancelPending tid with lookup tid (PS.monitors s) in saved
...   | nothing = case eq of λ ()
...   | just observer with PS.monitorDeliverable blocked (PS.pc observer) | PS.Pool.step PS.Pool.deliverCancel (PS.monitorPool s) in delivered
...     | true | just p′ with PS.detach err observer s in detached
...       | nothing = case eq of λ ()
...       | just (f , next) = case just-injective eq of λ { refl → M.thread-write next tid observer next-thread p′ saved′ refl refl others
  (T.keep-detached (C.capture next) tid observer next-thread p′ (X.Aux.monitorKeys (proj₂ (proj₂ next-held))) saved′ missing) next-held }
  where
  facts = detach err observer s detached held
  next-held = proj₁ facts
  saved′ = trans (cong (lookup tid) (proj₁ (proj₂ facts))) saved
  missing = proj₂ (proj₂ (proj₂ facts))
  handles = cancel-handles (PS.monitorPool s) tid phase delivered
  next-thread = record observer { pc = PS.cancelling; interrupted = just (record f { cancelError = err }); followup = lookup (PS.peerRef observer) (Sub.monitors (PS.machine s)) }
  others : ∀ uid → uid ≢ tid → lookup uid (PS.Pool.handles p′) ≡ lookup uid (PS.Pool.handles (PS.monitorPool next))
  others uid apart = trans (cong (lookup uid) handles) (trans
    (lookup-put-other tid uid PS.Pool.bodyUnwinding (PS.Pool.handles (PS.monitorPool s)) apart)
    (cong (λ pool → lookup uid (PS.Pool.handles pool)) (sym (proj₁ (proj₂ (proj₂ facts))))))
deliver-monitor blocked err s eq held | PS.Pool.cancelPending tid | just observer | false | pool = case eq of λ ()
deliver-monitor blocked err s eq held | PS.Pool.cancelPending tid | just observer | true | nothing = case eq of λ ()
deliver-monitor blocked err s eq held | PS.Pool.openPool = case eq of λ ()
deliver-monitor blocked err s eq held | PS.Pool.closing = case eq of λ ()
deliver-monitor blocked err s eq held | PS.Pool.closedPool = case eq of λ ()
deliver-monitor blocked err s eq held | PS.Pool.joinPending tid = case eq of λ ()

-- The concrete K labels retain the original PS masking/exception checks.
k-monitor-exception : ∀ tid err s {t} → K.step (K.peerStep (PS.monitorException tid err)) s ≡ just t → R.Reach s → R.Reach t
k-monitor-exception tid err = L.peer-lift (PS.monitorException tid err) (monitor-exception tid err)
k-monitor-cancel : ∀ err s {t} → K.step (K.peerStep (PS.deliverMonitorCancellation err)) s ≡ just t → R.Reach s → R.Reach t
k-monitor-cancel err = L.peer-lift (PS.deliverMonitorCancellation err) (deliver-monitor false err)
k-monitor-blocked-cancel : ∀ err s {t} → K.step (K.peerStep (PS.deliverBlockedMonitorCancellation err)) s ≡ just t → R.Reach s → R.Reach t
k-monitor-blocked-cancel err = L.peer-lift (PS.deliverBlockedMonitorCancellation err) (deliver-monitor true err)

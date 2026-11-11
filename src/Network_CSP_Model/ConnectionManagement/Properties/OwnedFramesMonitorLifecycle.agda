{-# OPTIONS --guardedness #-}

-- Monitor registration and body-exit lifecycle writes preserve exact owners.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesMonitorLifecycle
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesThreadUpdate as ThreadUpdate
import ConnectionManagement.Properties.OwnedFramesContext as ContextFacts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module X = Auxiliary isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module T = ThreadUpdate isBearerClosed isIOManagerError
  module V = ContextFacts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- A certified thread/pool write is exactly the named context writer.
thread-write : ∀ s tid old next p → lookup tid (PS.monitors s) ≡ just old →
  PS.worker next ≡ PS.worker old → PS.peerRef next ≡ PS.peerRef old →
  (∀ uid → uid ≢ tid → lookup uid (PS.Pool.handles p) ≡ lookup uid (PS.Pool.handles (PS.monitorPool s))) →
  T.KeepObserving (C.capture s) tid next p → D.Held s →
  D.Held (record s { monitors = put tid next (PS.monitors s); monitorPool = p })
thread-write s tid old next p saved worker peer others keep (inv , unique , aux) =
  T.update-inv (PS.cm s) (C.capture s) tid old next p (X.Aux.monitorKeys aux) saved worker peer others keep inv , unique ,
  T.update-aux (C.capture s) tid old next p saved worker peer others keep aux

-- Non-observing threads have no active followup obligation for their own handle.
stopped-write : ∀ s tid old nextPC p → lookup tid (PS.monitors s) ≡ just old → PS.pc old ≢ PS.observing →
  (∀ uid → uid ≢ tid → lookup uid (PS.Pool.handles p) ≡ lookup uid (PS.Pool.handles (PS.monitorPool s))) →
  D.Held s → D.Held (record s { monitors = put tid (record old { pc = nextPC }) (PS.monitors s); monitorPool = p })
stopped-write s tid old nextPC p saved stopped others held = thread-write s tid old (record old { pc = nextPC }) p saved refl refl others
  (T.keep-stopped (C.capture s) tid old (record old { pc = nextPC }) p (X.Aux.monitorKeys (proj₂ (proj₂ held))) saved stopped) held

-- Concurrent registration changes the registry but leaves all handle phases.
register-handles : ∀ tid p {p′} → PS.Pool.step (PS.Pool.registerConcurrent tid) p ≡ just p′ → PS.Pool.handles p′ ≡ PS.Pool.handles p
register-handles tid p eq with PS.Pool.phase p | lookup tid (PS.Pool.handles p) | PS.Pool.member tid (PS.Pool.registered p)
... | PS.Pool.openPool | just state | false with PS.Pool.awaitingRegistration state
...   | true = case just-injective eq of λ { refl → refl }
...   | false = case eq of λ ()
register-handles tid p eq | PS.Pool.openPool | nothing | member = case eq of λ ()
register-handles tid p eq | PS.Pool.openPool | just state | true = case eq of λ ()
register-handles tid p eq | PS.Pool.closing | handle | member = case eq of λ ()
register-handles tid p eq | PS.Pool.closedPool | handle | member = case eq of λ ()
register-handles tid p eq | PS.Pool.cancelPending j | handle | member = case eq of λ ()
register-handles tid p eq | PS.Pool.joinPending j | handle | member = case eq of λ ()

-- Registration updates only the masked parent's bookkeeping in the thread.
register-monitor : ∀ tid s {t} → PS.step (PS.registerMonitor tid) s ≡ just t → D.Held s → D.Held t
register-monitor tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.parentPC old | PS.Pool.step (PS.Pool.registerConcurrent tid) (PS.monitorPool s) in registered
...   | PS.created | just p′ = case just-injective eq of λ { refl → thread-write s tid old (record old { parentPC = PS.registered }) p′ saved refl refl
  (λ uid apart → cong (lookup uid) handles)
  (T.keep-stable (C.capture s) tid old (record old { parentPC = PS.registered }) p′
    (X.Aux.monitorKeys (proj₂ (proj₂ held))) saved refl handles) held }
  where handles = register-handles tid (PS.monitorPool s) registered
register-monitor tid s eq held | just old | PS.created | nothing = case eq of λ ()
register-monitor tid s eq held | just old | PS.registered | pool = case eq of λ ()
register-monitor tid s eq held | just old | PS.returned | pool = case eq of λ ()

-- In WithoutQueue, body return goes directly to normal deregistration pending.
returned-handles : ∀ tid result p {p′} → PS.Pool.step (PS.Pool.bodyReturnedWith tid result) p ≡ just p′ →
  PS.Pool.handles p′ ≡ put tid (PS.Pool.deregisterPending PS.Pool.normalExit) (PS.Pool.handles p)
returned-handles tid result p eq with lookup tid (PS.Pool.handles p)
... | just PS.Pool.bodyRunning = case just-injective eq of λ { refl → refl }
... | nothing = case eq of λ ()
... | just PS.Pool.bodyUnwinding = case eq of λ ()
... | just (PS.Pool.bodyReturned _) = case eq of λ ()
... | just (PS.Pool.deregisterPending _) = case eq of λ ()
... | just (PS.Pool.deregistered _) = case eq of λ ()
... | just (PS.Pool.resultAvailable _) = case eq of λ ()

-- Unwind completion has the corresponding cancelled-exit pending phase.
unwound-handles : ∀ tid p {p′} → PS.Pool.step (PS.Pool.bodyUnwound tid) p ≡ just p′ →
  PS.Pool.handles p′ ≡ put tid (PS.Pool.deregisterPending PS.Pool.cancelledExit) (PS.Pool.handles p)
unwound-handles tid p eq with lookup tid (PS.Pool.handles p)
... | just PS.Pool.bodyUnwinding = case just-injective eq of λ { refl → refl }
... | nothing = case eq of λ ()
... | just PS.Pool.bodyRunning = case eq of λ ()
... | just (PS.Pool.bodyReturned _) = case eq of λ ()
... | just (PS.Pool.deregisterPending _) = case eq of λ ()
... | just (PS.Pool.deregistered _) = case eq of λ ()
... | just (PS.Pool.resultAvailable _) = case eq of λ ()

-- Peer-world-only writes retain every caller and thread observation.
peer-rows-held : ∀ s rows → D.Held s → D.Held (PS.setMachine
  (record (PS.machine s) { world = record (Sub.world (PS.machine s)) { peers = rows } }) s)
peer-rows-held s rows (inv , unique , aux) =
  V.copy-inv (PS.cm s) (C.capture s) (C.capture target) inv , unique , V.copy-aux (C.capture s) (C.capture target) aux
  where target = PS.setMachine (record (PS.machine s) { world = record (Sub.world (PS.machine s)) { peers = rows } }) s

-- Peer-exit diagnostics alter no caller table or ownership observation.
finish-peer : ∀ clear ref s → D.Held s → D.Held (PS.finishPeer clear ref s)
finish-peer true ref s held with lookup ref (J.peers (Sub.world (PS.machine s)))
... | nothing = held
... | just peer = peer-rows-held s (put ref (record peer { monitorStarted = false; promotedAt = nothing }) (J.peers (Sub.world (PS.machine s)))) held
finish-peer false ref s held with lookup ref (J.peers (Sub.world (PS.machine s)))
... | nothing = held
... | just peer = peer-rows-held s (put ref (record peer { monitorStarted = false; promotedAt = Peer.promotedAt peer }) (J.peers (Sub.world (PS.machine s)))) held

-- The diagnostic peer write commutes with the independent thread/pool write.
finish-commute : ∀ clear ref s tid next p →
  PS.finishPeer clear ref (record s { monitors = put tid next (PS.monitors s); monitorPool = p }) ≡
  record (PS.finishPeer clear ref s) { monitors = put tid next (PS.monitors s); monitorPool = p }
finish-commute clear ref s tid next p with lookup ref (J.peers (Sub.world (PS.machine s)))
... | nothing = refl
... | just peer = refl

-- A finished body can change its own non-observing thread and then its peer flag.
finish-write : ∀ clear s tid old p → lookup tid (PS.monitors s) ≡ just old → PS.pc old ≢ PS.observing →
  (∀ uid → uid ≢ tid → lookup uid (PS.Pool.handles p) ≡ lookup uid (PS.Pool.handles (PS.monitorPool s))) →
  D.Held s → D.Held (record (PS.finishPeer clear (PS.peerRef old) s)
    { monitors = put tid (record old { pc = PS.exited }) (PS.monitors s); monitorPool = p })
finish-write clear s tid old p saved stopped others held = subst D.Held
  (finish-commute clear (PS.peerRef old) s tid (record old { pc = PS.exited }) p)
  (finish-peer clear (PS.peerRef old) (record s { monitors = put tid (record old { pc = PS.exited }) (PS.monitors s); monitorPool = p }) (stopped-write s tid old PS.exited p saved stopped others held))

-- Normal monitor return is separate from the body-return pool event.
finish-monitor : ∀ tid s {t} → PS.step (PS.finishMonitor tid) s ≡ just t → D.Held s → D.Held t
finish-monitor tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.pc old in phase | PS.Pool.step (PS.Pool.bodyReturnedWith tid nothing) (PS.monitorPool s) in returned
...   | PS.normalFinishing | just p′ = case just-injective eq of λ { refl → finish-write true s tid old p′ saved
  (λ equal → case trans (sym phase) equal of λ ())
  (λ uid apart → trans (cong (lookup uid) handles) (lookup-put-other tid uid (PS.Pool.deregisterPending PS.Pool.normalExit) (PS.Pool.handles (PS.monitorPool s)) apart)) held }
  where handles = returned-handles tid nothing (PS.monitorPool s) returned
finish-monitor tid s eq held | just old | PS.observing | pool = case eq of λ ()
finish-monitor tid s eq held | just old | PS.cancelling | pool = case eq of λ ()
finish-monitor tid s eq held | just old | PS.exited | pool = case eq of λ ()
finish-monitor tid s eq held | just old | (PS.errorWait err) | pool = case eq of λ ()
finish-monitor tid s eq held | just old | (PS.errorFinishing err) | pool = case eq of λ ()
finish-monitor tid s eq held | just old | PS.normalFinishing | nothing = case eq of λ ()

-- Error-handler return has the same physical exit boundary and pending phase.
finish-monitor-error : ∀ tid s {t} → PS.step (PS.finishMonitorError tid) s ≡ just t → D.Held s → D.Held t
finish-monitor-error tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.pc old in phase
...   | PS.errorFinishing err with PS.Pool.step (PS.Pool.bodyReturnedWith tid (just err)) (PS.monitorPool s) in returned
...     | nothing = case eq of λ ()
...     | just p′ = case just-injective eq of λ { refl → finish-write true s tid old p′ saved
  (λ equal → case trans (sym phase) equal of λ ())
  (λ uid apart → trans (cong (lookup uid) handles) (lookup-put-other tid uid (PS.Pool.deregisterPending PS.Pool.normalExit) (PS.Pool.handles (PS.monitorPool s)) apart)) held }
  where handles = returned-handles tid (just err) (PS.monitorPool s) returned
finish-monitor-error tid s eq held | just old | PS.observing = case eq of λ ()
finish-monitor-error tid s eq held | just old | PS.normalFinishing = case eq of λ ()
finish-monitor-error tid s eq held | just old | PS.cancelling = case eq of λ ()
finish-monitor-error tid s eq held | just old | PS.exited = case eq of λ ()
finish-monitor-error tid s eq held | just old | (PS.errorWait err) = case eq of λ ()

-- A cancelled monitor body must finish its real detached cancellation first.
monitor-body-unwound : ∀ tid s {t} → PS.step (PS.monitorBodyUnwound tid) s ≡ just t → D.Held s → D.Held t
monitor-body-unwound tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.pc old in phase | PS.interrupted old
...   | PS.cancelling | just f with Cancel.pc f
...     | Cancel.finished Cancel.abandoned with PS.Pool.step (PS.Pool.bodyUnwound tid) (PS.monitorPool s) in unwound
...       | nothing = case eq of λ ()
...       | just p′ = case just-injective eq of λ { refl → finish-write false s tid old p′ saved
  (λ equal → case trans (sym phase) equal of λ ())
  (λ uid apart → trans (cong (lookup uid) handles) (lookup-put-other tid uid (PS.Pool.deregisterPending PS.Pool.cancelledExit) (PS.Pool.handles (PS.monitorPool s)) apart)) held }
  where handles = unwound-handles tid (PS.monitorPool s) unwound
monitor-body-unwound tid s eq held | just old | PS.cancelling | just f | Cancel.cleaning active = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.cancelling | just f | Cancel.finished Cancel.cleanupComplete = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.cancelling | just f | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.observing | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.normalFinishing | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.exited | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | (PS.errorWait err) | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | (PS.errorFinishing err) | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.cancelling | nothing = case eq of λ ()

{-# OPTIONS --guardedness #-}

-- Immutable-worker monitor lifecycle and parent-continuation adapters.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedCallersLifecycle
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Properties.OwnedCallersBase as Base
import ConnectionManagement.Properties.OwnedFramesMonitorLifecycle as LifecycleFacts
import ConnectionManagement.Properties.OwnedFramesEstablishment as EstablishmentFacts
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
open Base isBearerClosed isIOManagerError using
  (module PS; module GP; module C; PeerNF; thread-update; job-update)
private
  module Old = LifecycleFacts isBearerClosed isIOManagerError
  module E = EstablishmentFacts isBearerClosed isIOManagerError
  module X = Auxiliary isBearerClosed isIOManagerError

-- Physical pool and peer diagnostic fields do not affect thread replacement.
thread-write : ∀ s tid old next p → lookup tid (PS.monitors s) ≡ just old → PS.worker next ≡ PS.worker old →
  PeerNF s → PeerNF (record s { monitors = put tid next (PS.monitors s); monitorPool = p })
thread-write s tid old next p found worker held = thread-update (PS.cm s) (C.capture s) tid old next found worker held

-- The diagnostic peer write retains all source and historical caller fields.
finish-peer : ∀ clear ref s → PeerNF s → PeerNF (PS.finishPeer clear ref s)
finish-peer true ref s held with lookup ref (J.peers (Sub.world (PS.machine s)))
... | nothing = held
... | just peer = held
finish-peer false ref s held with lookup ref (J.peers (Sub.world (PS.machine s)))
... | nothing = held
... | just peer = held

-- Reuse the diagnostic-write commutation lemma to keep the proof component-sized.
finish-write : ∀ clear s tid old p → lookup tid (PS.monitors s) ≡ just old → PeerNF s →
  PeerNF (record (PS.finishPeer clear (PS.peerRef old) s)
    { monitors = put tid (record old { pc = PS.exited }) (PS.monitors s); monitorPool = p })
finish-write clear s tid old p saved held = subst PeerNF
  (Old.finish-commute clear (PS.peerRef old) s tid (record old { pc = PS.exited }) p)
  (finish-peer clear (PS.peerRef old) (record s { monitors = put tid (record old { pc = PS.exited }) (PS.monitors s); monitorPool = p })
    (thread-write s tid old (record old { pc = PS.exited }) p saved refl held))

-- Registration keeps the historical worker of the selected thread.
register-monitor : ∀ tid s {t} → PS.step (PS.registerMonitor tid) s ≡ just t → PeerNF s → PeerNF t
register-monitor tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.parentPC old | PS.Pool.step (PS.Pool.registerConcurrent tid) (PS.monitorPool s) in registered
...   | PS.created | just p′ = case just-injective eq of λ { refl → thread-write s tid old (record old { parentPC = PS.registered }) p′ saved refl held }
register-monitor tid s eq held | just old | PS.created | nothing = case eq of λ ()
register-monitor tid s eq held | just old | PS.registered | pool = case eq of λ ()
register-monitor tid s eq held | just old | PS.returned | pool = case eq of λ ()


-- Normal body return retains the worker and finishes peer diagnostics.
finish-monitor : ∀ tid s {t} → PS.step (PS.finishMonitor tid) s ≡ just t → PeerNF s → PeerNF t
finish-monitor tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.pc old in phase | PS.Pool.step (PS.Pool.bodyReturnedWith tid nothing) (PS.monitorPool s) in returned
...   | PS.normalFinishing | just p′ = case just-injective eq of λ { refl → finish-write true s tid old p′ saved held }
finish-monitor tid s eq held | just old | PS.observing | pool = case eq of λ ()
finish-monitor tid s eq held | just old | PS.cancelling | pool = case eq of λ ()
finish-monitor tid s eq held | just old | PS.exited | pool = case eq of λ ()
finish-monitor tid s eq held | just old | (PS.errorWait err) | pool = case eq of λ ()
finish-monitor tid s eq held | just old | (PS.errorFinishing err) | pool = case eq of λ ()
finish-monitor tid s eq held | just old | PS.normalFinishing | nothing = case eq of λ ()


-- Error-handler return retains the same historical monitor identity.
finish-monitor-error : ∀ tid s {t} → PS.step (PS.finishMonitorError tid) s ≡ just t → PeerNF s → PeerNF t
finish-monitor-error tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.pc old in phase
...   | PS.errorFinishing err with PS.Pool.step (PS.Pool.bodyReturnedWith tid (just err)) (PS.monitorPool s) in returned
...     | nothing = case eq of λ ()
...     | just p′ = case just-injective eq of λ { refl → finish-write true s tid old p′ saved held }
finish-monitor-error tid s eq held | just old | PS.observing = case eq of λ ()
finish-monitor-error tid s eq held | just old | PS.normalFinishing = case eq of λ ()
finish-monitor-error tid s eq held | just old | PS.cancelling = case eq of λ ()
finish-monitor-error tid s eq held | just old | PS.exited = case eq of λ ()
finish-monitor-error tid s eq held | just old | (PS.errorWait err) = case eq of λ ()


-- Cancellation completion retains the worker after actual detached unwind.
monitor-body-unwound : ∀ tid s {t} → PS.step (PS.monitorBodyUnwound tid) s ≡ just t → PeerNF s → PeerNF t
monitor-body-unwound tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.pc old in phase | PS.interrupted old
...   | PS.cancelling | just f with Cancel.pc f
...     | Cancel.finished Cancel.abandoned with PS.Pool.step (PS.Pool.bodyUnwound tid) (PS.monitorPool s) in unwound
...       | nothing = case eq of λ ()
...       | just p′ = case just-injective eq of λ { refl → finish-write false s tid old p′ saved held }
monitor-body-unwound tid s eq held | just old | PS.cancelling | just f | Cancel.cleaning active = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.cancelling | just f | Cancel.finished Cancel.cleanupComplete = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.cancelling | just f | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.observing | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.normalFinishing | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.exited | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | (PS.errorWait err) | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | (PS.errorFinishing err) | interrupted = case eq of λ ()
monitor-body-unwound tid s eq held | just old | PS.cancelling | nothing = case eq of λ ()

-- The two parent writes retain both the job caller and monitor worker.
establish-write : ∀ s j jf tid t → lookup j (Sub.jobs (PS.machine s)) ≡ just jf →
  PS.byParent j (PS.monitors s) ≡ just (tid , t) → X.Aux (C.capture s) → PeerNF s → PeerNF (E.establish-target s j jf tid t)
establish-write s j jf tid t saved parent aux held =
  thread-update (PS.cm s) job-context tid t (record t { parentPC = PS.returned }) thread-saved refl
    (job-update (PS.cm s) (C.capture s) j jf next-job saved refl held)
  where
  next-job = record jf { execution = record (Sub.execution jf) { pc = J.complete (G.establishedOK (PS.peerRef t)) } }
  job-context = C.capture (PS.setMachine (record (PS.machine s) { jobs = put j next-job (Sub.jobs (PS.machine s)) }) s)
  thread-saved = E.parent-lookup j (PS.monitors s) (X.Aux.monitorKeys aux) tid t parent

-- The parent returns only after registration and keeps both caller identities.
return-establishment : ∀ j s {t} → PS.step (PS.returnEstablishment j) s ≡ just t → X.Aux (C.capture s) → PeerNF s → PeerNF t
return-establishment j s eq aux held with PS.byParent j (PS.monitors s) in parent | lookup j (Sub.jobs (PS.machine s)) in saved
... | just (tid , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf) in pc | GP.running j (GP.pool (PS.governor s))
...   | PS.registered | J.forkMonitor | true = case just-injective eq of λ { refl → establish-write s j jf tid t saved parent aux held }
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.begin | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.awaitAcquire | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | (J.startBundle temp ns) | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | (J.publishBundle temp) | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.markWarm | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.finishActivation | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.awaitHot | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.awaitAll | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.callRelease | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.awaitRelease | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.delayFailure | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | (J.awaitCold result) | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | (J.complete result) | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | (J.acquirePolicy fault) | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | (J.nodeDelivery fault) | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | (J.nodeRethrow fault) | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.created | pc | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.returned | pc | running = case eq of λ ()
return-establishment j s eq aux held | just (tid , t) | just jf | PS.registered | J.forkMonitor | false = case eq of λ ()
return-establishment j s eq aux held | nothing | any = case eq of λ ()
return-establishment j s eq aux held | just pair | nothing = case eq of λ ()

-- Physical establishment completion changes pool metadata only.
finish-establishment : ∀ j s {t} → PS.step (PS.finishEstablishment j) s ≡ just t → PeerNF s → PeerNF t
finish-establishment j s eq held with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s)) in saved
... | just pair | just jf with PS.parentPC (proj₂ pair) | J.pc (Sub.execution jf) in pc
...   | PS.returned | J.complete result with GP.Pool.step
  (GP.Pool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (PS.governor s)) in returned
...     | nothing = case eq of λ ()
...     | just p′ = case just-injective eq of λ { refl → held }
finish-establishment j s eq held | just pair | just jf | PS.returned | J.begin = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.awaitAcquire = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.startBundle temp ns) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.publishBundle temp) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.markWarm = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.finishActivation = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.awaitHot = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.awaitAll = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.callRelease = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.awaitRelease = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.delayFailure = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.awaitCold result) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.acquirePolicy fault) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.nodeDelivery fault) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | (J.nodeRethrow fault) = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.returned | J.forkMonitor = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.created | pc = case eq of λ ()
finish-establishment j s eq held | just pair | just jf | PS.registered | pc = case eq of λ ()
finish-establishment j s eq held | nothing | any = case eq of λ ()
finish-establishment j s eq held | just pair | nothing = case eq of λ ()

-- Error commit changes the peer status and the thread PC, keeping its worker.
commit-error : ∀ tid s {t} → PS.step (PS.commitMonitorError tid) s ≡ just t → PeerNF s → PeerNF t
commit-error tid s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just old with PS.pc old in phase | lookup (PS.peerRef old) (J.peers (Sub.world (PS.machine s)))
...   | PS.errorWait err | just peer with Peer.demoted (Peer.key peer) (PS.shared s)
...     | false = case eq of λ ()
...     | true = case just-injective eq of λ { refl → thread-write before tid old (record old { pc = PS.errorFinishing err }) (PS.monitorPool s) saved refl held }
  where
  rows = put (PS.peerRef old) (record peer { status = Peer.peerCold }) (J.peers (Sub.world (PS.machine s)))
  before = PS.setMachine (record (PS.machine s) { world = record (Sub.world (PS.machine s)) { peers = rows } }) s
commit-error tid s eq held | just t | PS.observing | peer = case eq of λ ()
commit-error tid s eq held | just t | PS.normalFinishing | peer = case eq of λ ()
commit-error tid s eq held | just t | PS.cancelling | peer = case eq of λ ()
commit-error tid s eq held | just t | PS.exited | peer = case eq of λ ()
commit-error tid s eq held | just t | (PS.errorFinishing err) | peer = case eq of λ ()
commit-error tid s eq held | just t | PS.errorWait err | nothing = case eq of λ ()


{-# OPTIONS --guardedness #-}

-- PSA threads never change their captured worker; pool allocation cannot
-- overwrite a live frame owner. Cancellation only removes source frames.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedCallersPeers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (ident)
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.OutboundKeys using (fields-same)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Properties.OwnedCallersBase as Base
import ConnectionManagement.Properties.OwnedCallersGovernor as GovernorFacts
import ConnectionManagement.Properties.OwnedCallersCancel as CancelNF
import ConnectionManagement.Properties.OwnedCallersLifecycle as LifecycleNF
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesThreads as ThreadFacts
import ConnectionManagement.Properties.OwnedFramesForkMonitor as ForkFacts
import ConnectionManagement.Properties.PeerSupervisionSupply as SupplyFacts
import ConnectionManagement.Properties.PeerJobFrames as RowFacts
open Base isBearerClosed isIOManagerError using
  (module PS; module GP; module C; PeerNF; thread-update; thread-birth; copy-peer)
open Frames isBearerClosed isIOManagerError using (Inv)
private
  module Governor = GovernorFacts isBearerClosed isIOManagerError
  module D = CancelNF isBearerClosed isIOManagerError
  module Life = LifecycleNF isBearerClosed isIOManagerError
  module X = Auxiliary isBearerClosed isIOManagerError
  module Threads = ThreadFacts isIOManagerError
  module Fork = ForkFacts isBearerClosed isIOManagerError
  module Supply = SupplyFacts isIOManagerError
  module Rows = RowFacts isIOManagerError

-- Only raw subsystem core aliases need the pre-existing peer-route refusal.
allowed : PS.Action → Bool
allowed (PS.run a) = Governor.allowed a
allowed _ = true

-- Poll bookkeeping changes a thread's PC but preserves its captured worker.
note-poll : ∀ ref before after → PS.monitors after ≡ PS.monitors before → X.Aux (C.capture before) →
  PeerNF after → PeerNF (PS.notePoll ref before after)
note-poll ref before after rows aux held with PS.byPeer ref (PS.monitors before) in selected |
  lookup ref (J.peers (Sub.world (PS.machine before))) | lookup ref (J.peers (Sub.world (PS.machine after)))
... | just (tid , t) | just old | just next with Peer.monitorStarted next
...   | true = held
...   | false = thread-update (PS.cm after) (C.capture after) tid t
  (record t { pc = PS.afterPoll (lookup ref (Sub.monitors (PS.machine after))) })
  (trans (cong (lookup tid) rows) (Threads.byPeer-lookup ref (PS.monitors before) (X.Aux.monitorKeys aux) tid t selected)) refl held
note-poll ref before after rows aux held | nothing | _ | _ = held
note-poll ref before after rows aux held | just _ | nothing | _ = held
note-poll ref before after rows aux held | just _ | just _ | nothing = held

-- noteGovernor's sole observed write is the immutable-worker poll update.
note-governor : ∀ a before after → PS.monitors after ≡ PS.monitors before → X.Aux (C.capture before) →
  PeerNF after → PeerNF (PS.noteGovernor a before after)
note-governor (GP.run (Sub.pollPeer ref w)) before after rows aux held = note-poll ref before after rows aux held
note-governor (GP.run (Sub.core a)) before after rows aux held = held
note-governor (GP.run (Sub.publishPublicState)) before after rows aux held = held
note-governor (GP.run (Sub.sampleTime t)) before after rows aux held = held
note-governor (GP.run (Sub.applyAt t)) before after rows aux held = held
note-governor (GP.run (Sub.setTargets desired)) before after rows aux held = held
note-governor (GP.run (Sub.selectMonitor delays)) before after rows aux held = held
note-governor (GP.run (Sub.selectCompletion)) before after rows aux held = held
note-governor (GP.run (Sub.selectTargets)) before after rows aux held = held
note-governor (GP.run (Sub.selectWakeup)) before after rows aux held = held
note-governor (GP.run (Sub.registerWakeup)) before after rows aux held = held
note-governor (GP.run (Sub.expireWakeup)) before after rows aux held = held
note-governor (GP.run (Sub.cancelWakeup)) before after rows aux held = held
note-governor (GP.run (Sub.publishCounters)) before after rows aux held = held
note-governor (GP.run (Sub.traceSelection)) before after rows aux held = held
note-governor (GP.run (Sub.selectPolicy picked)) before after rows aux held = held
note-governor (GP.run (Sub.forkJob w child sock)) before after rows aux held = held
note-governor (GP.run (Sub.registerJob)) before after rows aux held = held
note-governor (GP.run (Sub.finishLaunch)) before after rows aux held = held
note-governor (GP.run (Sub.jobStep j a)) before after rows aux held = held
note-governor (GP.run (Sub.enqueueCompletion j delay)) before after rows aux held = held
note-governor (GP.run (Sub.deregisterJob j)) before after rows aux held = held
note-governor (GP.run (Sub.protocolResult ref n result)) before after rows aux held = held
note-governor (GP.run (Sub.publishInitiatorResult ref n)) before after rows aux held = held
note-governor (GP.run (Sub.monitorStep ref a)) before after rows aux held = held
note-governor (GP.run (Sub.monitorFinished ref)) before after rows aux held = held
note-governor (GP.run (Sub.observeInitiatorFailure ref)) before after rows aux held = held
note-governor (GP.handoff w) before after rows aux held = held
note-governor (GP.beginClose js) before after rows aux held = held
note-governor (GP.requestCancel) before after rows aux held = held
note-governor (GP.join) before after rows aux held = held
note-governor (GP.finishClose) before after rows aux held = held
note-governor (GP.deliverCancellation err) before after rows aux held = held
note-governor (GP.deliverOpenCancellation err) before after rows aux held = held
note-governor (GP.cleanup j a) before after rows aux held = held
note-governor (GP.bodyUnwound j) before after rows aux held = held
note-governor (GP.recoverCloseFailure j) before after rows aux held = held
note-governor (GP.deregisterCancelled j) before after rows aux held = held
note-governor (GP.publishAsyncResult j) before after rows aux held = held

-- Physical forks retain the CM source and restore the original parent row.
fork-monitor : ∀ j w s {t} → PS.fork j w s ≡ just t → Inv (PS.cm s) (C.capture s) → X.Aux (C.capture s) → PeerNF s → PeerNF t
fork-monitor j (ident n) s eq inv aux held with lookup j (Sub.jobs (PS.machine s)) in saved | PS.byParent j (PS.monitors s) | PS.freshWorker (ident n) s in worker-free
... | just jf | nothing | true with G.kind (J.work (Sub.execution jf)) | J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s)) |
  PS.byPeer (J.connectionRef (Sub.execution jf)) (PS.monitors s) in peer-free
...   | G.establish | J.forkMonitor | true | nothing with Sub.advance (Sub.jobStep j J.launchMonitor) (PS.machine s) in spawned |
  PS.Pool.step (PS.Pool.forkConcurrent (ident n)) (PS.monitorPool s) in forked
...     | just c′ | just p′ = case just-injective eq of λ { refl →
  copy-peer born target (fields-same (PS.cm born) (PS.cm target)
    (cong O.acquiring source) (cong O.releasing source) (cong O.acquired source) (cong O.released source)) rows refl
    (thread-birth (PS.cm s) (C.capture s) (ident n) next-thread (Fork.pool-fresh (ident n) (PS.monitorPool s) forked) inv aux held) }
  where
  next-thread = PS.thread (J.connectionRef (Sub.execution jf)) (ident n) j PS.created PS.observing nothing nothing
  born = record s { monitors = put (ident n) next-thread (PS.monitors s); monitorPool = p′ }
  target = record (PS.setMachine (record c′ { jobs = put j jf (Sub.jobs c′) }) s)
    { monitorPool = p′; monitors = put (ident n) next-thread (PS.monitors s) }
  source = Supply.sub-launch-cm j (PS.machine s) spawned
  rows = trans (Rows.fork-rows j (PS.machine s) spawned jf) (Fork.put-existing j jf (Sub.jobs (PS.machine s)) saved)
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | nothing | any = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | just c′ | nothing = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.forget | pc | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.activate | pc | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.close | pc | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.deactivate | pc | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.begin | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.awaitAcquire | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | (J.startBundle temp ns) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | (J.publishBundle temp) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.markWarm | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.finishActivation | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.awaitHot | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.awaitAll | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.callRelease | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.awaitRelease | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.delayFailure | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | (J.awaitCold result) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | (J.complete result) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | (J.acquirePolicy fault) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | (J.nodeDelivery fault) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | (J.nodeRethrow fault) | running | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.forkMonitor | false | peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | true | G.establish | J.forkMonitor | true | just peer = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | nothing | any | fresh = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | just previous | fresh = case eq of λ ()
fork-monitor j (ident n) s eq inv aux held | just jf | nothing | false = case eq of λ ()


-- Detach keeps both historical ownership tables while deleting active frames.
detach : ∀ err observer s {f next} → PS.detach err observer s ≡ just (f , next) → PeerNF s →
  PeerNF next × PS.monitors next ≡ PS.monitors s
detach err observer s eq held with lookup (PS.worker observer) (O.acquiring (PS.cm s))
... | just _ = case eq of λ ()
... | nothing with lookup (PS.peerRef observer) (Sub.monitors (PS.machine s))
...   | nothing with Cancel.start (PS.worker observer) err Cancel.ordinary (PS.cm s) in started
...     | nothing = case eq of λ ()
...     | just (f , c′) = case just-injective eq of λ { refl → D.start-nf (PS.worker observer) err Cancel.ordinary (PS.cm s) started (C.capture s) held , refl }
detach err observer s eq held | nothing | just follow with J.caller follow ≟ PS.worker observer
... | no _ = case eq of λ ()
... | yes _ with Cancel.start (PS.worker observer) err Cancel.ordinary (PS.cm s) in started
...   | nothing = case eq of λ ()
...   | just (f , c′) = case just-injective eq of λ { refl → D.start-nf (PS.worker observer) err Cancel.ordinary (PS.cm s) started (C.capture s) held , refl }

-- Error delivery changes only the selected thread's mutable fields after detach.
monitor-exception : ∀ tid err s {t} → PS.step (PS.monitorException tid err) s ≡ just t → PeerNF s → PeerNF t
monitor-exception tid err s eq held with lookup tid (PS.monitors s) in saved
... | nothing = case eq of λ ()
... | just observer with PS.bodyActive tid observer s | PS.detach err observer s in detached
...   | true | just (f , next) = case just-injective eq of λ { refl → Life.thread-write next tid observer
  (record observer { pc = PS.errorWait err; interrupted = just f; followup = lookup (PS.peerRef observer) (Sub.monitors (PS.machine s)) })
  (PS.monitorPool next) (trans (cong (lookup tid) (proj₂ facts)) saved) refl (proj₁ facts) }
  where facts = detach err observer s detached held
monitor-exception tid err s eq held | just observer | false | _ = case eq of λ ()
monitor-exception tid err s eq held | just observer | true | nothing = case eq of λ ()

-- Both asynchronous delivery modes retain the selected monitor's worker.
deliver-monitor : ∀ blocked err s {t} → PS.deliverMonitor blocked err s ≡ just t → PeerNF s → PeerNF t
deliver-monitor blocked err s eq held with PS.Pool.phase (PS.monitorPool s)
... | PS.Pool.cancelPending tid with lookup tid (PS.monitors s) in saved
...   | nothing = case eq of λ ()
...   | just observer with PS.monitorDeliverable blocked (PS.pc observer) | PS.Pool.step PS.Pool.deliverCancel (PS.monitorPool s)
...     | true | just p′ with PS.detach err observer s in detached
...       | nothing = case eq of λ ()
...       | just (f , next) = case just-injective eq of λ { refl → Life.thread-write next tid observer
  (record observer { pc = PS.cancelling; interrupted = just (record f { cancelError = err }); followup = lookup (PS.peerRef observer) (Sub.monitors (PS.machine s)) }) p′
  (trans (cong (lookup tid) (proj₂ facts)) saved) refl (proj₁ facts) }
  where facts = detach err observer s detached held
deliver-monitor blocked err s eq held | PS.Pool.cancelPending tid | just observer | false | _ = case eq of λ ()
deliver-monitor blocked err s eq held | PS.Pool.cancelPending tid | just observer | true | nothing = case eq of λ ()

deliver-monitor blocked err s eq held | PS.Pool.openPool = case eq of λ ()
deliver-monitor blocked err s eq held | PS.Pool.closing = case eq of λ ()
deliver-monitor blocked err s eq held | PS.Pool.closedPool = case eq of λ ()
deliver-monitor blocked err s eq held | PS.Pool.joinPending j = case eq of λ ()

-- Every actual scope constructor mirrors its own dispatcher with-tree.
scope-step : ∀ a s {t} → PS.step (PS.scope a) s ≡ just t → PeerNF s → PeerNF t
scope-step Scope.deliverCancel s eq held with Scope.cursor (PS.scopes s) | GP.Pool.parentFork (GP.pool (PS.governor s))
... | Scope.closing Scope.governor | just j = case eq of λ ()
scope-step Scope.deliverCancel s eq held | Scope.closing Scope.governor | nothing with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.deliverCancel s eq held | Scope.openScope | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.deliverCancel s eq held | Scope.readyToFinish | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.deliverCancel s eq held | Scope.finishedScope | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.deliverCancel s eq held | Scope.closing Scope.churn | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.deliverCancel s eq held | Scope.closing Scope.localRoot | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.deliverCancel s eq held | Scope.closing Scope.ledger | any with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.beginUnwind s eq held with Scope.step (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.requestCancel s eq held with Scope.step (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.join s eq held with Scope.step (PS.governorPoolClosed s) Scope.join (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step Scope.finishClose s eq held with Scope.step (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step (Scope.bodyExit actor) s eq held with Scope.step (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step (Scope.publishResult actor) s eq held with Scope.step (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }
scope-step (Scope.beginFailure actor) s eq held with Scope.step (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → held }


-- All selected PSA actions preserve the additional invariant using Reach's
-- owner and attachment clauses only at the relevant allocation/begin boundary.
peer-safe : ∀ a s {t} → allowed a ≡ true → PS.step a s ≡ just t →
  Inv (PS.cm s) (C.capture s) → X.Aux (C.capture s) → PeerNF s → PeerNF t
peer-safe (PS.run a) s ok eq inv aux held with PS.governorAllowed a s
... | false = case eq of λ ()
... | true with GP.step a (PS.governor s) in advanced
...   | nothing = case eq of λ ()
...   | just g′ = case just-injective eq of λ { refl → note-governor a s (record s { governor = g′ }) refl aux
  (Governor.governor-safe a s ok advanced inv aux held) }
peer-safe (PS.forkMonitor j w) s ok eq inv aux held = fork-monitor j w s eq inv aux held
peer-safe (PS.registerMonitor tid) s ok eq inv aux held = Life.register-monitor tid s eq held
peer-safe (PS.returnEstablishment j) s ok eq inv aux held = Life.return-establishment j s eq aux held
peer-safe (PS.finishEstablishment j) s ok eq inv aux held = Life.finish-establishment j s eq held
peer-safe (PS.monitorException tid err) s ok eq inv aux held = monitor-exception tid err s eq held
peer-safe (PS.commitMonitorError tid) s ok eq inv aux held = Life.commit-error tid s eq held
peer-safe (PS.finishMonitorError tid) s ok eq inv aux held = Life.finish-monitor-error tid s eq held
peer-safe (PS.finishMonitor tid) s ok eq inv aux held = Life.finish-monitor tid s eq held
peer-safe (PS.scope a) s ok eq inv aux held = scope-step a s eq held
peer-safe (PS.deliverMonitorCancellation err) s ok eq inv aux held = deliver-monitor false err s eq held
peer-safe (PS.deliverBlockedMonitorCancellation err) s ok eq inv aux held = deliver-monitor true err s eq held
peer-safe (PS.monitorBodyUnwound tid) s ok eq inv aux held = Life.monitor-body-unwound tid s eq held
peer-safe (PS.beginMonitorClose js) s ok eq inv aux held with Scope.closed (PS.scopes s)
... | false = case eq of λ ()
... | true with PS.Pool.step (PS.Pool.beginClose js) (PS.monitorPool s)
...   | nothing = case eq of λ ()
...   | just p′ = case just-injective eq of λ { refl → held }
peer-safe PS.requestMonitorCancel s ok eq inv aux held with PS.Pool.step PS.Pool.requestCancel (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }
peer-safe PS.joinMonitor s ok eq inv aux held with PS.Pool.step PS.Pool.join (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }
peer-safe PS.finishMonitorClose s ok eq inv aux held with PS.Pool.step PS.Pool.finishClose (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }
peer-safe (PS.deregisterMonitor j) s ok eq inv aux held with PS.Pool.step (PS.Pool.deregister j) (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }
peer-safe (PS.publishMonitorResult j) s ok eq inv aux held with PS.Pool.step (PS.Pool.publishAsyncResult j) (PS.monitorPool s)
... | nothing = case eq of λ ()
... | just p′ = case just-injective eq of λ { refl → held }

{-# OPTIONS --guardedness #-}

-- Three operational metadata projections of real coupled peer supervision.
-- CM/peer writes are retained in the source run; no full-source erasure is claimed.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.PeerSupervision (isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.PeerSupervision as Supervision
module PS = Supervision isIOManagerError
module GP = PS.GP
module GPool = GP.Pool
module BPool = PS.Pool
import ConnectionManagement.Properties.GovernorPool as GovernorProof
module Gov = GovernorProof isIOManagerError
import ConnectionManagement.Properties.JobPoolClose as GovernorClose
module GClose = GovernorClose GP.Body
import ConnectionManagement.Properties.JobPoolCloseKernel as BackgroundClose
module BClose = BackgroundClose (Maybe ErrorId) false
import ConnectionManagement.Properties.AsyncScope as ScopeProof
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as CM

record View : Set where
  constructor viewOf
  field gov : GPool.State
        bg : BPool.State
        scopes : Scope.State
open View public
view : PS.State → View
view s = viewOf (GP.pool (PS.governor s)) (PS.monitorPool s) (PS.scopes s)

GTrace : GPool.State → GPool.State → Set
GTrace p q = Σ (List GPool.Action) (λ as → GPool.Executes p as q)
BTrace : BPool.State → BPool.State → Set
BTrace p q = Σ (List BPool.Action) (λ as → BPool.Executes p as q)
STrace : Scope.State → Scope.State → Set
STrace p q = Σ (List Scope.Action) (λ as → Scope.Executes p as q)
record Paths (v w : View) : Set where
  constructor paths
  field governor : GTrace (gov v) (gov w)
        background : BTrace (bg v) (bg w)
        coordinator : STrace (scopes v) (scopes w)
open Paths public
idle : ∀ v → Paths v v
idle v = paths ([] , GPool.done) ([] , BPool.done) ([] , Scope.done)
right-view : ∀ {v w w′} → w ≡ w′ → Paths v w → Paths v w′
right-view refl evidence = evidence
onlyG : ∀ v {p′} → GTrace (gov v) p′ → Paths v (record v { gov = p′ })
onlyG v trace = paths trace ([] , BPool.done) ([] , Scope.done)
onlyB : ∀ v {p′} → BTrace (bg v) p′ → Paths v (record v { bg = p′ })
onlyB v trace = paths ([] , GPool.done) trace ([] , Scope.done)
onlyS : ∀ v {p′} → STrace (scopes v) p′ → Paths v (record v { scopes = p′ })
onlyS v trace = paths ([] , GPool.done) ([] , BPool.done) trace
oneG : ∀ action p {p′} → GPool.step action p ≡ just p′ → GTrace p p′
oneG a p eq = (a ∷ []) , GPool.next eq GPool.done
oneB : ∀ action p {p′} → BPool.step action p ≡ just p′ → BTrace p p′
oneB a p eq = (a ∷ []) , BPool.next eq BPool.done
oneS : ∀ gate action p {p′} → Scope.step gate action p ≡ just p′ → STrace p p′
oneS gate a p eq = (a ∷ []) , Scope.next eq Scope.done

-- These functions may change real source peer/CM state, while leaving exactly
-- the three projected metadata components unchanged.
finish-view : ∀ clear ref s → view (PS.finishPeer clear ref s) ≡ view s
finish-view clear ref s with lookup ref (J.peers (Sub.world (PS.machine s)))
... | nothing = refl
... | just peer = refl
poll-view : ∀ ref before after → view (PS.notePoll ref before after) ≡ view after
poll-view ref before after with PS.byPeer ref (PS.monitors before) |
  lookup ref (J.peers (Sub.world (PS.machine before))) | lookup ref (J.peers (Sub.world (PS.machine after)))
... | just (tid , t) | just old | just next with Peer.monitorStarted next
...   | false = refl
...   | true = refl
poll-view ref before after | nothing | _ | _ = refl
poll-view ref before after | just (tid , t) | nothing | _ = refl
poll-view ref before after | just (tid , t) | just old | nothing = refl
note-view : ∀ action before after → view (PS.noteGovernor action before after) ≡ view after
note-view (GP.run (Sub.pollPeer ref w)) before after = poll-view ref before after
note-view (GP.run (Sub.core a)) before after = refl
note-view (GP.run Sub.publishPublicState) before after = refl
note-view (GP.run (Sub.sampleTime t)) before after = refl
note-view (GP.run (Sub.applyAt t)) before after = refl
note-view (GP.run (Sub.setTargets target)) before after = refl
note-view (GP.run (Sub.selectMonitor delay)) before after = refl
note-view (GP.run Sub.selectCompletion) before after = refl
note-view (GP.run Sub.selectTargets) before after = refl
note-view (GP.run Sub.selectWakeup) before after = refl
note-view (GP.run Sub.registerWakeup) before after = refl
note-view (GP.run Sub.expireWakeup) before after = refl
note-view (GP.run Sub.cancelWakeup) before after = refl
note-view (GP.run Sub.publishCounters) before after = refl
note-view (GP.run Sub.traceSelection) before after = refl
note-view (GP.run (Sub.selectPolicy picked)) before after = refl
note-view (GP.run (Sub.forkJob caller child sock)) before after = refl
note-view (GP.run Sub.registerJob) before after = refl
note-view (GP.run Sub.finishLaunch) before after = refl
note-view (GP.run (Sub.jobStep j a)) before after = refl
note-view (GP.run (Sub.enqueueCompletion j delay)) before after = refl
note-view (GP.run (Sub.deregisterJob j)) before after = refl
note-view (GP.run (Sub.protocolResult ref n result)) before after = refl
note-view (GP.run (Sub.publishInitiatorResult ref i)) before after = refl
note-view (GP.run (Sub.monitorStep ref a)) before after = refl
note-view (GP.run (Sub.monitorFinished ref)) before after = refl
note-view (GP.run (Sub.observeInitiatorFailure ref)) before after = refl
note-view (GP.handoff w) before after = refl
note-view (GP.beginClose order) before after = refl
note-view GP.requestCancel before after = refl
note-view GP.join before after = refl
note-view GP.finishClose before after = refl
note-view (GP.deliverCancellation err) before after = refl
note-view (GP.deliverOpenCancellation err) before after = refl
note-view (GP.cleanup j a) before after = refl
note-view (GP.bodyUnwound j) before after = refl
note-view (GP.recoverCloseFailure j) before after = refl
note-view (GP.deregisterCancelled j) before after = refl
note-view (GP.publishAsyncResult j) before after = refl

detach-view : ∀ err t s {f s′} → PS.detach err t s ≡ just (f , s′) → view s′ ≡ view s
detach-view err t s eq with lookup (PS.worker t) (CM.acquiring (PS.cm s))
... | just active = case eq of λ ()
... | nothing with lookup (PS.peerRef t) (Sub.monitors (PS.machine s))
...   | nothing with Cancel.start (PS.worker t) err Cancel.ordinary (PS.cm s)
...     | just (f , c′) = case just-injective eq of λ { refl → refl }
...     | nothing = case eq of λ ()
detach-view err t s eq | nothing | just follow with J.caller follow ≟ PS.worker t
... | no _ = case eq of λ ()
... | yes _ with Cancel.start (PS.worker t) err Cancel.ordinary (PS.cm s)
...   | nothing = case eq of λ ()
...   | just (f , c′) = case just-injective eq of λ { refl → refl }

fork-projects : ∀ j w s {s′} → PS.fork j w s ≡ just s′ → Paths (view s) (view s′)
fork-projects j (ident wid) s eq with lookup j (Sub.jobs (PS.machine s)) | PS.byParent j (PS.monitors s) | PS.freshWorker (ident wid) s
... | just jf | nothing | true with G.kind (J.work (Sub.execution jf)) |
  J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s)) |
  PS.byPeer (J.connectionRef (Sub.execution jf)) (PS.monitors s)
...   | G.establish | J.forkMonitor | true | nothing with
  Sub.advance (Sub.jobStep j J.launchMonitor) (PS.machine s) |
  BPool.step (BPool.forkConcurrent (ident wid)) (PS.monitorPool s) in forked
...     | just c′ | just p′ = case just-injective eq of λ { refl →
  onlyB (view s) (oneB (BPool.forkConcurrent (ident wid)) (PS.monitorPool s) forked) }
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | nothing | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | just c′ | nothing = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.forget | _ | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.activate | _ | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.close | _ | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.deactivate | _ | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.begin | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitAcquire | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.startBundle temp ns) | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.publishBundle temp) | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.markWarm | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.finishActivation | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitHot | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitAll | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.callRelease | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitRelease | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.delayFailure | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.awaitCold result) | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.complete result) | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.acquirePolicy fault) | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.nodeDelivery fault) | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.nodeRethrow fault) | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | false | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | true | just found = case eq of λ ()
fork-projects j (ident wid) s eq | nothing | _ | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | just found | _ = case eq of λ ()
fork-projects j (ident wid) s eq | just jf | nothing | false = case eq of λ ()

monitor-delivery-projects : ∀ blocked err s {s′} → PS.deliverMonitor blocked err s ≡ just s′ → Paths (view s) (view s′)
monitor-delivery-projects blocked err s eq with BPool.phase (PS.monitorPool s)
... | BPool.cancelPending tid with lookup tid (PS.monitors s)
...   | nothing = case eq of λ ()
...   | just t with PS.monitorDeliverable blocked (PS.pc t) | BPool.step BPool.deliverCancel (PS.monitorPool s) in delivered
...     | true | just p′ with PS.detach err t s in detached
...       | just (f , s′) = case just-injective eq of λ { refl →
  right-view (sym (cong (λ v → record v { bg = p′ }) (detach-view err t s detached)))
    (onlyB (view s) (oneB BPool.deliverCancel (PS.monitorPool s) delivered)) }
...       | nothing = case eq of λ ()
monitor-delivery-projects blocked err s eq | BPool.cancelPending tid | just t | false | _ = case eq of λ ()
monitor-delivery-projects blocked err s eq | BPool.cancelPending tid | just t | true | nothing = case eq of λ ()
monitor-delivery-projects blocked err s eq | BPool.openPool = case eq of λ ()
monitor-delivery-projects blocked err s eq | BPool.closing = case eq of λ ()
monitor-delivery-projects blocked err s eq | BPool.closedPool = case eq of λ ()
monitor-delivery-projects blocked err s eq | BPool.joinPending tid = case eq of λ ()

-- Every accepted action has real component paths; direct establishment return
-- contributes a governor body-return step rather than inventing a GP dispatch.
step-projects : ∀ action s {s′} → PS.step action s ≡ just s′ → Paths (view s) (view s′)
step-projects (PS.run a) s eq with PS.governorAllowed a s
... | false = case eq of λ ()
... | true with GP.step a (PS.governor s) in stepped
...   | nothing = case eq of λ ()
...   | just g′ = case just-injective eq of λ { refl →
  right-view (sym (note-view a s (record s { governor = g′ })))
    (onlyG (view s) (Gov.step-projects a (PS.governor s) stepped)) }
step-projects (PS.forkMonitor j w) s eq = fork-projects j w s eq
step-projects (PS.registerMonitor tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.parentPC t | BPool.step (BPool.registerConcurrent tid) (PS.monitorPool s) in registered
...   | PS.created | just p′ = case just-injective eq of λ { refl →
  onlyB (view s) (oneB (BPool.registerConcurrent tid) (PS.monitorPool s) registered) }
step-projects (PS.registerMonitor tid) s eq | just t | PS.created | nothing = case eq of λ ()
step-projects (PS.registerMonitor tid) s eq | just t | PS.registered | _ = case eq of λ ()
step-projects (PS.registerMonitor tid) s eq | just t | PS.returned | _ = case eq of λ ()
step-projects (PS.registerMonitor tid) s eq | nothing = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
... | just (tid , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s))
...   | PS.registered | J.forkMonitor | true = case just-injective eq of λ { refl → idle (view s) }
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.created | _ | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.returned | _ | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.begin | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitAcquire | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.startBundle temp ns) | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.publishBundle temp) | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.markWarm | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.finishActivation | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitHot | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitAll | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.callRelease | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitRelease | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.delayFailure | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.awaitCold result) | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.complete result) | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.acquirePolicy fault) | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.nodeDelivery fault) | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.nodeRethrow fault) | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.forkMonitor | false = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | nothing | _ = case eq of λ ()
step-projects (PS.returnEstablishment j) s eq | just found | nothing = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
... | just (_ , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf)
...   | PS.returned | J.complete result with GPool.step
    (GPool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (PS.governor s)) in returned
...     | just p′ = case just-injective eq of λ { refl →
  onlyG (view s) (oneG (GPool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (PS.governor s)) returned) }
...     | nothing = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.created | _ = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.registered | _ = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.begin = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitAcquire = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.startBundle temp ns) = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.publishBundle temp) = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.markWarm = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.forkMonitor = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.finishActivation = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitHot = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitAll = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.callRelease = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitRelease = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.delayFailure = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.awaitCold result) = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.acquirePolicy fault) = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.nodeDelivery fault) = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.nodeRethrow fault) = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | nothing | _ = case eq of λ ()
step-projects (PS.finishEstablishment j) s eq | just found | nothing = case eq of λ ()
step-projects (PS.monitorException tid err) s eq with lookup tid (PS.monitors s)
... | just t with PS.bodyActive tid t s | PS.detach err t s in detached
...   | true | just (f , s′) = case just-injective eq of λ { refl → right-view (sym (detach-view err t s detached)) (idle (view s)) }
step-projects (PS.monitorException tid err) s eq | just t | false | _ = case eq of λ ()
step-projects (PS.monitorException tid err) s eq | just t | true | nothing = case eq of λ ()
step-projects (PS.monitorException tid err) s eq | nothing = case eq of λ ()
step-projects (PS.commitMonitorError tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t | lookup (PS.peerRef t) (J.peers (Sub.world (PS.machine s)))
...   | PS.errorWait err | just peer with Peer.demoted (Peer.key peer) (PS.shared s)
...     | true = case just-injective eq of λ { refl → idle (view s) }
...     | false = case eq of λ ()
step-projects (PS.commitMonitorError tid) s eq | just t | PS.errorWait err | nothing = case eq of λ ()
step-projects (PS.commitMonitorError tid) s eq | just t | PS.observing | _ = case eq of λ ()
step-projects (PS.commitMonitorError tid) s eq | just t | PS.normalFinishing | _ = case eq of λ ()
step-projects (PS.commitMonitorError tid) s eq | just t | PS.cancelling | _ = case eq of λ ()
step-projects (PS.commitMonitorError tid) s eq | just t | PS.exited | _ = case eq of λ ()
step-projects (PS.commitMonitorError tid) s eq | just t | (PS.errorFinishing err) | _ = case eq of λ ()
step-projects (PS.commitMonitorError tid) s eq | nothing = case eq of λ ()
step-projects (PS.finishMonitor tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t | BPool.step (BPool.bodyReturnedWith tid nothing) (PS.monitorPool s) in returned
...   | PS.normalFinishing | just p′ = case just-injective eq of λ { refl →
  right-view (sym (cong (λ v → record v { bg = p′ }) (finish-view true (PS.peerRef t) s)))
    (onlyB (view s) (oneB (BPool.bodyReturnedWith tid nothing) (PS.monitorPool s) returned)) }
step-projects (PS.finishMonitor tid) s eq | just t | PS.normalFinishing | nothing = case eq of λ ()
step-projects (PS.finishMonitor tid) s eq | just t | PS.observing | _ = case eq of λ ()
step-projects (PS.finishMonitor tid) s eq | just t | PS.cancelling | _ = case eq of λ ()
step-projects (PS.finishMonitor tid) s eq | just t | PS.exited | _ = case eq of λ ()
step-projects (PS.finishMonitor tid) s eq | just t | (PS.errorWait err) | _ = case eq of λ ()
step-projects (PS.finishMonitor tid) s eq | just t | (PS.errorFinishing err) | _ = case eq of λ ()
step-projects (PS.finishMonitor tid) s eq | nothing = case eq of λ ()
step-projects (PS.finishMonitorError tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t
...   | PS.errorFinishing err with BPool.step (BPool.bodyReturnedWith tid (just err)) (PS.monitorPool s) in returned
...     | just p′ = case just-injective eq of λ { refl →
  right-view (sym (cong (λ v → record v { bg = p′ }) (finish-view true (PS.peerRef t) s)))
    (onlyB (view s) (oneB (BPool.bodyReturnedWith tid (just err)) (PS.monitorPool s) returned)) }
...     | nothing = case eq of λ ()
step-projects (PS.finishMonitorError tid) s eq | just t | PS.observing = case eq of λ ()
step-projects (PS.finishMonitorError tid) s eq | just t | PS.normalFinishing = case eq of λ ()
step-projects (PS.finishMonitorError tid) s eq | just t | PS.cancelling = case eq of λ ()
step-projects (PS.finishMonitorError tid) s eq | just t | PS.exited = case eq of λ ()
step-projects (PS.finishMonitorError tid) s eq | just t | (PS.errorWait err) = case eq of λ ()
step-projects (PS.finishMonitorError tid) s eq | nothing = case eq of λ ()
step-projects (PS.scope Scope.deliverCancel) s eq with Scope.cursor (PS.scopes s) | GPool.parentFork (GP.pool (PS.governor s))
... | Scope.closing Scope.governor | just pending = case eq of λ ()
step-projects (PS.scope Scope.deliverCancel) s eq | Scope.openScope | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.churn | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.localRoot | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.ledger | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.governor | nothing with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.deliverCancel) s eq | Scope.readyToFinish | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.deliverCancel) s eq | Scope.finishedScope | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.beginUnwind) s eq with Scope.step (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.requestCancel) s eq with Scope.step (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.join) s eq with Scope.step (PS.governorPoolClosed s) Scope.join (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.join (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope Scope.finishClose) s eq with Scope.step (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope (Scope.beginFailure actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope (Scope.bodyExit actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.scope (Scope.publishResult actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s) in advanced
... | just next = case just-injective eq of λ { refl → onlyS (view s) (oneS (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.beginMonitorClose order) s eq with Scope.closed (PS.scopes s)
... | false = case eq of λ ()
... | true with BPool.step (BPool.beginClose order) (PS.monitorPool s) in advanced
...   | just p′ = case just-injective eq of λ { refl → onlyB (view s) (oneB (BPool.beginClose order) (PS.monitorPool s) advanced) }
...   | nothing = case eq of λ ()
step-projects PS.requestMonitorCancel s eq with BPool.step BPool.requestCancel (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → onlyB (view s) (oneB BPool.requestCancel (PS.monitorPool s) advanced) }
... | nothing = case eq of λ ()
step-projects PS.joinMonitor s eq with BPool.step BPool.join (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → onlyB (view s) (oneB BPool.join (PS.monitorPool s) advanced) }
... | nothing = case eq of λ ()
step-projects PS.finishMonitorClose s eq with BPool.step BPool.finishClose (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → onlyB (view s) (oneB BPool.finishClose (PS.monitorPool s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.deregisterMonitor tid) s eq with BPool.step (BPool.deregister tid) (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → onlyB (view s) (oneB (BPool.deregister tid) (PS.monitorPool s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.publishMonitorResult tid) s eq with BPool.step (BPool.publishAsyncResult tid) (PS.monitorPool s) in advanced
... | just p′ = case just-injective eq of λ { refl → onlyB (view s) (oneB (BPool.publishAsyncResult tid) (PS.monitorPool s) advanced) }
... | nothing = case eq of λ ()
step-projects (PS.deliverMonitorCancellation err) s eq = monitor-delivery-projects false err s eq
step-projects (PS.deliverBlockedMonitorCancellation err) s eq = monitor-delivery-projects true err s eq
step-projects (PS.monitorBodyUnwound tid) s eq with lookup tid (PS.monitors s)
... | just t with PS.pc t | PS.interrupted t
...   | PS.cancelling | just f with Cancel.pc f
...     | Cancel.finished Cancel.abandoned with BPool.step (BPool.bodyUnwound tid) (PS.monitorPool s) in advanced
...       | just p′ = case just-injective eq of λ { refl →
  right-view (sym (cong (λ v → record v { bg = p′ }) (finish-view false (PS.peerRef t) s)))
    (onlyB (view s) (oneB (BPool.bodyUnwound tid) (PS.monitorPool s) advanced)) }
...       | nothing = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | just f | Cancel.cleaning active = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | just f | Cancel.finished Cancel.cleanupComplete = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | just f | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | nothing = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.observing | _ = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.normalFinishing | _ = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.exited | _ = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | just t | (PS.errorWait err) | _ = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | just t | (PS.errorFinishing err) | _ = case eq of λ ()
step-projects (PS.monitorBodyUnwound tid) s eq | nothing = case eq of λ ()

appendG : ∀ {p as q bs r} → GPool.Executes p as q → GPool.Executes q bs r → GPool.Executes p (as ++ bs) r
appendG GPool.done right = right
appendG (GPool.next eq left) right = GPool.next eq (appendG left right)
appendB : ∀ {p as q bs r} → BPool.Executes p as q → BPool.Executes q bs r → BPool.Executes p (as ++ bs) r
appendB BPool.done right = right
appendB (BPool.next eq left) right = BPool.next eq (appendB left right)
appendS : ∀ {p as q bs r} → Scope.Executes p as q → Scope.Executes q bs r → Scope.Executes p (as ++ bs) r
appendS Scope.done right = right
appendS (Scope.next eq left) right = Scope.next eq (appendS left right)
compose : ∀ {v w z} → Paths v w → Paths w z → Paths v z
compose (paths (ga , gp) (ba , bp) (sa , sp)) (paths (ga′ , gp′) (ba′ , bp′) (sa′ , sp′)) =
  paths ((ga ++ ga′) , appendG gp gp′) ((ba ++ ba′) , appendB bp bp′) ((sa ++ sa′) , appendS sp sp′)
exec-projects : ∀ {s actions s′} → PS.Executes s actions s′ → Paths (view s) (view s′)
exec-projects PS.done = idle _
exec-projects (PS.next {s = s} {a = a} eq path) = compose (step-projects a s eq) (exec-projects path)

-- This certificate is conditional on real finite execution and actual closure
-- of each component. It neither proves eventual closure nor remaining CM scopes.
from-initial : ∀ {c g actions s} → PS.Executes (PS.initial c g) actions s →
  GPool.phase (GP.pool (PS.governor s)) ≡ GPool.closedPool →
  BPool.phase (PS.monitorPool s) ≡ BPool.closedPool →
  Scope.cursor (PS.scopes s) ≡ Scope.finishedScope →
  (∀ j → j ∈ GPool.snapshot (GP.pool (PS.governor s)) → GClose.Terminal (GP.pool (PS.governor s)) j) ×
  (∀ tid → tid ∈ BPool.snapshot (PS.monitorPool s) → BClose.Terminal (PS.monitorPool s) tid) ×
  ScopeProof.AllJoined (PS.scopes s)
from-initial path governorClosed backgroundClosed scopesClosed with exec-projects path
... | paths (ga , gp) (ba , bp) (sa , sp) =
  GClose.from-initial gp governorClosed , BClose.from-initial bp backgroundClosed , ScopeProof.from-initial sp scopesClosed

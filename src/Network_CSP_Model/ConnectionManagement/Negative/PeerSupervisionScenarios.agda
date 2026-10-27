{-# OPTIONS --guardedness #-}

-- Physical PSA registry and outer-scope controls. The first path is initialized;
-- later explicit two-parent/status/release snapshots test local source windows
-- and are not additional source reachability or whole-node shutdown theorems.
module ConnectionManagement.Negative.PeerSupervisionScenarios where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.Properties.AsyncScope as ScopeFacts
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.State as S
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.CSP.OutboundAdmission as O
import ConnectionManagement.CSP.OutboundReleaseScenarios as Release
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.Negative.GovernorPool as Prior
open import ConnectionManagement.Scenarios.Admission using (key₀)

module PS = Supervision Prior.classify
module GP = PS.GP
module Pool = PS.Pool
j₀ j₁ tid₀ tid₁ : JobId
j₀ = ident 0
j₁ = ident 1
tid₀ = ident 50
tid₁ = ident 51
monitorWorker secondWorker : WorkerId
monitorWorker = ident 50
secondWorker = ident 51
wrap : GP.State → PS.State
wrap g = PS.supervising g [] Pool.initial Scope.initial
p₀ : PS.State
p₀ = PS.initial (CM.initial F.start) L.settings
p1 : PS.State
p1 = wrap Prior.g1
p2 : PS.State
p2 = wrap Prior.g2
p3 : PS.State
p3 = wrap Prior.g3
p4 : PS.State
p4 = wrap Prior.g4
p5 : PS.State
p5 = wrap Prior.g5
p6 : PS.State
p6 = wrap Prior.g6
p7 : PS.State
p7 = wrap Prior.g7
p8 : PS.State
p8 = wrap Prior.g8
p9 : PS.State
p9 = wrap Prior.g9
p10 : PS.State
p10 = wrap Prior.g10
p11 : PS.State
p11 = wrap Prior.g11
p12 : PS.State
p12 = wrap Prior.g12
p13 : PS.State
p13 = wrap Prior.g13
p14 : PS.State
p14 = wrap Prior.g14
p15 : PS.State
p15 = wrap Prior.g15
p16 : PS.State
p16 = wrap Prior.g16
p17 : PS.State
p17 = wrap Prior.g17
p18 : PS.State
p18 = wrap Prior.g18
p19 : PS.State
p19 = wrap Prior.g19
handed : PS.State
handed = wrap Prior.handed
p20 : PS.State
p20 = wrap (record (Prior.live L.c20 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p21 : PS.State
p21 = wrap (record (Prior.live L.c21 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p22 : PS.State
p22 = wrap (record (Prior.live L.c22 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p23 : PS.State
p23 = wrap (record (Prior.live L.c23 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p24 : PS.State
p24 = wrap (record (Prior.live L.c24 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p25 : PS.State
p25 = wrap (record (Prior.live L.c25 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p26 : PS.State
p26 = wrap (record (Prior.live L.c26 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p27 : PS.State
p27 = wrap (record (Prior.live L.c27 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p28 : PS.State
p28 = wrap (record (Prior.live L.c28 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p29 : PS.State
p29 = wrap (record (Prior.live L.c29 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p30 : PS.State
p30 = wrap (record (Prior.live L.c30 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p31 : PS.State
p31 = wrap (record (Prior.live L.c31 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p32 : PS.State
p32 = wrap (record (Prior.live L.c32 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p33 : PS.State
p33 = wrap (record (Prior.live L.c33 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p34 : PS.State
p34 = wrap (record (Prior.live L.c34 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p35 : PS.State
p35 = wrap (record (Prior.live L.c35 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p36 : PS.State
p36 = wrap (record (Prior.live L.c36 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p37 : PS.State
p37 = wrap (record (Prior.live L.c37 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p38 : PS.State
p38 = wrap (record (Prior.live L.c38 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
p39 : PS.State
p39 = wrap (record (Prior.live L.c39 Prior.runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
sourcePrefix : List PS.Action
sourcePrefix = (PS.run (GP.run L.a1)) ∷ (PS.run (GP.run L.a2)) ∷ (PS.run (GP.run L.a3)) ∷ (PS.run (GP.run L.a4)) ∷ (PS.run (GP.run L.a5)) ∷ (PS.run (GP.run L.a6)) ∷ (PS.run (GP.run L.a7)) ∷ (PS.run (GP.run L.a8)) ∷ (PS.run (GP.run L.a9)) ∷ (PS.run (GP.run L.a10)) ∷ (PS.run (GP.run L.a11)) ∷ (PS.run (GP.run L.a12)) ∷ (PS.run (GP.run L.a13)) ∷ (PS.run (GP.run L.a14)) ∷ (PS.run (GP.run L.a15)) ∷ (PS.run (GP.run L.a16)) ∷ (PS.run (GP.run L.a17)) ∷ (PS.run (GP.run L.a18)) ∷ (PS.run (GP.run L.a19)) ∷ (PS.run (GP.handoff L.caller)) ∷ (PS.run (GP.run L.a20)) ∷ (PS.run (GP.run L.a21)) ∷ (PS.run (GP.run L.a22)) ∷ (PS.run (GP.run L.a23)) ∷ (PS.run (GP.run L.a24)) ∷ (PS.run (GP.run L.a25)) ∷ (PS.run (GP.run L.a26)) ∷ (PS.run (GP.run L.a27)) ∷ (PS.run (GP.run L.a28)) ∷ (PS.run (GP.run L.a29)) ∷ (PS.run (GP.run L.a30)) ∷ (PS.run (GP.run L.a31)) ∷ (PS.run (GP.run L.a32)) ∷ (PS.run (GP.run L.a33)) ∷ (PS.run (GP.run L.a34)) ∷ (PS.run (GP.run L.a35)) ∷ (PS.run (GP.run L.a36)) ∷ (PS.run (GP.run L.a37)) ∷ (PS.run (GP.run L.a38)) ∷ (PS.run (GP.run L.a39)) ∷ []
-- Keep checked execution evidence opaque to downstream certificate reduction.
abstract
  initialized-pre-fork : PS.Executes p₀ sourcePrefix p39
  initialized-pre-fork = PS.next {s₁ = p1} refl (PS.next {s₁ = p2} refl (PS.next {s₁ = p3} refl (PS.next {s₁ = p4} refl (PS.next {s₁ = p5} refl (PS.next {s₁ = p6} refl (PS.next {s₁ = p7} refl (PS.next {s₁ = p8} refl (PS.next {s₁ = p9} refl (PS.next {s₁ = p10} refl (PS.next {s₁ = p11} refl (PS.next {s₁ = p12} refl (PS.next {s₁ = p13} refl (PS.next {s₁ = p14} refl (PS.next {s₁ = p15} refl (PS.next {s₁ = p16} refl (PS.next {s₁ = p17} refl (PS.next {s₁ = p18} refl (PS.next {s₁ = p19} refl (PS.next {s₁ = handed} refl (PS.next {s₁ = p20} refl (PS.next {s₁ = p21} refl (PS.next {s₁ = p22} refl (PS.next {s₁ = p23} refl (PS.next {s₁ = p24} refl (PS.next {s₁ = p25} refl (PS.next {s₁ = p26} refl (PS.next {s₁ = p27} refl (PS.next {s₁ = p28} refl (PS.next {s₁ = p29} refl (PS.next {s₁ = p30} refl (PS.next {s₁ = p31} refl (PS.next {s₁ = p32} refl (PS.next {s₁ = p33} refl (PS.next {s₁ = p34} refl (PS.next {s₁ = p35} refl (PS.next {s₁ = p36} refl (PS.next {s₁ = p37} refl (PS.next {s₁ = p38} refl (PS.next {s₁ = p39} refl (PS.done))))))))))))))))))))))))))))))))))))))))

after : PS.Action → PS.State → PS.State
after a s with PS.step a s
... | nothing = s
... | just s′ = s′
-- Explicit snapshots keep acceptance conversion local to each component.
physicalThread : PS.ParentPC → PS.MonitorPC → Maybe Cancel.Frame → PS.Thread
physicalThread parentPC pc interrupted = PS.thread (ident 0) monitorWorker j₀ parentPC pc interrupted nothing
m1 m2 m3 m4 : PS.State
m1 = record (PS.setMachine (record L.c40 { jobs = Sub.jobs L.c39 }) p39)
  { monitors = (tid₀ , physicalThread PS.created PS.observing nothing) ∷ []
  ; monitorPool = record Pool.initial { handles = (tid₀ , Pool.bodyRunning) ∷ [] } }
m2 = record m1 { monitors = (tid₀ , physicalThread PS.registered PS.observing nothing) ∷ []
  ; monitorPool = record (PS.monitorPool m1) { registered = tid₀ ∷ [] } }
m3 = record (PS.setMachine L.c40 m2)
  { monitors = (tid₀ , physicalThread PS.returned PS.observing nothing) ∷ [] }
m4 = record m3 { governor = record (PS.governor m3) { pool = record Prior.runningPool
  { handles = (j₀ , GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0)))) ∷ [] } } }
physical-fork : PS.step (PS.forkMonitor j₀ monitorWorker) p39 ≡ just m1
physical-fork = refl
physical-register : PS.step (PS.registerMonitor tid₀) m1 ≡ just m2
physical-register = refl
psa-return : PS.step (PS.returnEstablishment j₀) m2 ≡ just m3
psa-return = refl
governor-body-return : PS.step (PS.finishEstablishment j₀) m3 ≡ just m4
governor-body-return = refl
fork-captures-worker : lookup tid₀ (PS.monitors m1) ≡ just
  (PS.thread (ident 0) monitorWorker j₀ PS.created PS.observing nothing nothing)
fork-captures-worker = refl
registration-before-psa-return : PS.step (PS.returnEstablishment j₀) m1 ≡ nothing
registration-before-psa-return = refl
psa-return-before-job-body-return : lookup j₀ (GP.Pool.handles (GP.pool (PS.governor m3))) ≡ just GP.Pool.bodyRunning
psa-return-before-job-body-return = refl
body-return-captures-real-outcome : lookup j₀ (GP.Pool.handles (GP.pool (PS.governor m4))) ≡ just
  (GP.Pool.bodyReturned (GP.body j₀ Prior.work (G.establishedOK (ident 0))))
body-return-captures-real-outcome = refl
raw-launch-cannot-bypass-registry : PS.step (PS.run (GP.run L.a40)) p39 ≡ nothing
raw-launch-cannot-bypass-registry = refl
fresh-worker-cannot-be-parent : PS.step (PS.forkMonitor j₀ L.caller) p39 ≡ nothing
fresh-worker-cannot-be-parent = refl
fresh-worker-cannot-be-handler : PS.step (PS.forkMonitor j₀ L.child) p39 ≡ nothing
fresh-worker-cannot-be-handler = refl

append : ∀ {s as t bs u} → PS.Executes s as t → PS.Executes t bs u → PS.Executes s (as ++ bs) u
append PS.done right = right
append (PS.next eq left) right = PS.next eq (append left right)
spawnActions : List PS.Action
spawnActions = PS.forkMonitor j₀ monitorWorker ∷ PS.registerMonitor tid₀ ∷
  PS.returnEstablishment j₀ ∷ PS.finishEstablishment j₀ ∷ []
-- Keep checked execution evidence opaque to downstream certificate reduction.
abstract
  spawn-path : PS.Executes p39 spawnActions m4
  spawn-path = PS.next physical-fork (PS.next physical-register (PS.next psa-return (PS.next governor-body-return PS.done)))
-- Keep checked execution evidence opaque to downstream certificate reduction.
abstract
  initialized-spawn : PS.Executes p₀ (sourcePrefix ++ spawnActions) m4
  initialized-spawn = append initialized-pre-fork spawn-path

-- The source bracket ends at PSA return, before the outer job-body return.
waitingGovernor : JobId → PS.State → PS.State
waitingGovernor j s = record s { governor = record (PS.governor s)
  { pool = record (GP.pool (PS.governor s))
    { phase = GP.Pool.cancelPending j; snapshot = j ∷ []; remaining = j ∷ [] } } }
cancelParent : PS.State → PS.State
cancelParent s = after (PS.run (GP.deliverCancellation (errorId 9))) (waitingGovernor j₀ s)
masked-parent-refuses-delivery : PS.step (PS.run (GP.deliverCancellation (errorId 9))) (waitingGovernor j₀ m1) ≡ nothing
masked-parent-refuses-delivery = refl
registered-parent-delivery : PS.step (PS.run (GP.deliverCancellation (errorId 9))) (waitingGovernor j₀ m2) ≡ just (cancelParent m2)
registered-parent-delivery = refl
beforeReturnUnwound afterReturnUnwound : PS.State
beforeReturnUnwound = after (PS.run (GP.bodyUnwound j₀)) (cancelParent m2)
afterReturnUnwound = after (PS.run (GP.bodyUnwound j₀)) (cancelParent m3)
before-psa-return-unwinds : PS.step (PS.run (GP.bodyUnwound j₀)) (cancelParent m2) ≡ just beforeReturnUnwound
before-psa-return-unwinds = refl
after-psa-return-delivery : PS.step (PS.run (GP.deliverCancellation (errorId 9))) (waitingGovernor j₀ m3) ≡ just (cancelParent m3)
after-psa-return-delivery = refl
after-psa-return-unwinds : PS.step (PS.run (GP.bodyUnwound j₀)) (cancelParent m3) ≡ just afterReturnUnwound
after-psa-return-unwinds = refl
peerAt : PeerConnectionId → PS.State → Maybe Peer.Peer
peerAt ref s = lookup ref (J.peers (Sub.world (PS.machine s)))
before-return-restores-cold : peerAt (ident 0) beforeReturnUnwound ≡ just (record L.p10 { status = Peer.peerCold })
before-return-restores-cold = refl
after-return-preserves-warm : peerAt (ident 0) afterReturnUnwound ≡ just L.p10
after-return-preserves-warm = refl
independent-monitor-remains-registered : Pool.registered (PS.monitorPool beforeReturnUnwound) ≡ tid₀ ∷ []
independent-monitor-remains-registered = refl

-- These two-parent snapshots are conditional; distinct jobs and captured peer
-- references share one registry, with independent per-parent registration masks.
twoParents : PS.State
twoParents = PS.setMachine (record L.c39
  { jobs = (j₁ , Sub.jobFrame (J.frame (G.job G.establish L.peerAddr nothing)
      (ident 20) (ident 21) (ident 20) (ident 1) J.forkMonitor) false false) ∷ Sub.jobs L.c39
  ; pool = j₁ ∷ j₀ ∷ []
  ; world = record (Sub.world L.c39) { peers = ((ident 1) , L.p9) ∷ J.peers (Sub.world L.c39) } })
  (record p39 { governor = record (PS.governor p39)
    { pool = record Prior.runningPool
      { handles = (j₁ , GP.Pool.bodyRunning) ∷ GP.Pool.handles Prior.runningPool
      ; registered = j₁ ∷ j₀ ∷ [] } } })
twoFork1 twoFork2 secondRegistered secondCancelled : PS.State
twoFork1 = after (PS.forkMonitor j₀ monitorWorker) twoParents
twoFork2 = after (PS.forkMonitor j₁ secondWorker) twoFork1
secondRegistered = after (PS.registerMonitor tid₁) twoFork2
secondCancelled = after (PS.run (GP.deliverCancellation (errorId 9))) (waitingGovernor j₁ secondRegistered)
first-parent-forks : PS.step (PS.forkMonitor j₀ monitorWorker) twoParents ≡ just twoFork1
first-parent-forks = refl
second-parent-forks-during-first-gap : PS.step (PS.forkMonitor j₁ secondWorker) twoFork1 ≡ just twoFork2
second-parent-forks-during-first-gap = refl
second-parent-registers-independently : PS.step (PS.registerMonitor tid₁) twoFork2 ≡ just secondRegistered
second-parent-registers-independently = refl
second-cancellation-not-blocked-by-first-mask : PS.step (PS.run (GP.deliverCancellation (errorId 9))) (waitingGovernor j₁ secondRegistered) ≡ just secondCancelled
second-cancellation-not-blocked-by-first-mask = refl
first-parent-still-masked : PS.step (PS.run (GP.deliverCancellation (errorId 9))) (waitingGovernor j₀ secondRegistered) ≡ nothing
first-parent-still-masked = refl

-- A physical worker is bound to its captured peer; supplying a fresh caller
-- cannot make a raw poll/followup run on behalf of a different thread.
wrong-poll-caller : PS.step (PS.run (GP.run (Sub.pollPeer (ident 0) (ident 99)))) m4 ≡ nothing
wrong-poll-caller = refl
unregistered-peer-poll-refused : PS.step (PS.run (GP.run (Sub.pollPeer (ident 1) monitorWorker))) m4 ≡ nothing
unregistered-peer-poll-refused = refl
captured-worker-cannot-begin-free-release : PS.step (PS.run (GP.run (Sub.core (CM.beginRelease monitorWorker key₀)))) m4 ≡ nothing
captured-worker-cannot-begin-free-release = refl
withPeer : Peer.Peer → PS.State → PS.State
withPeer p s = PS.setMachine (record (PS.machine s) { world = record (Sub.world (PS.machine s))
  { peers = put (ident 0) p (J.peers (Sub.world (PS.machine s))) } }) s
coldPeer hotPeer : Peer.Peer
coldPeer = record L.p10 { status = Peer.peerCold; promotedAt = just 42 }
hotPeer = record L.p10 { status = Peer.peerHot; hotControl = Peer.quiesce; promotedAt = just 42 }
coldPoll : PS.State → PS.State
coldPoll s = after (PS.run (GP.run (Sub.pollPeer (ident 0) monitorWorker))) (withPeer coldPeer s)
normal-finish-boundary : PS.step (PS.run (GP.run (Sub.pollPeer (ident 0) monitorWorker))) (withPeer coldPeer m4) ≡ just (coldPoll m4)
normal-finish-boundary = refl
normal-duration-not-yet-traced : peerAt (ident 0) (coldPoll m4) ≡ just coldPeer
normal-duration-not-yet-traced = refl
normalFinished : PS.State
normalFinished = after (PS.finishMonitor tid₀) (coldPoll m4)
normal-exit : PS.step (PS.finishMonitor tid₀) (coldPoll m4) ≡ just normalFinished
normal-exit = refl
normal-clears-promotion-time : peerAt (ident 0) normalFinished ≡ just (record coldPeer { monitorStarted = false; promotedAt = nothing })
normal-clears-promotion-time = refl
normal-no-governor-queue : Sub.completions (PS.machine normalFinished) ≡ []
normal-no-governor-queue = refl
fastChildFinished : PS.State
fastChildFinished = after (PS.finishMonitor tid₀) (coldPoll m1)
fast-child-before-registration : PS.step (PS.finishMonitor tid₀) (coldPoll m1) ≡ just fastChildFinished
fast-child-before-registration = refl
fast-child-deregistration-retries : PS.step (PS.deregisterMonitor tid₀) fastChildFinished ≡ nothing
fast-child-deregistration-retries = refl
fast-child-parent-can-still-register : PS.step (PS.registerMonitor tid₀) fastChildFinished ≡ just
  (after (PS.registerMonitor tid₀) fastChildFinished)
fast-child-parent-can-still-register = refl
monitor-started-false-is-not-async-result : lookup tid₀ (Pool.handles (PS.monitorPool normalFinished)) ≡ just (Pool.deregisterPending Pool.normalExit)
monitor-started-false-is-not-async-result = refl

-- Synchronous errors first block in the source demotion transaction. Async
-- cancellation during that interruptible wait does not commit its Cold write.
errorWaiting : PS.State
errorWaiting = after (PS.monitorException tid₀ (errorId 8)) (withPeer hotPeer m4)
sync-error-enters-wait : PS.step (PS.monitorException tid₀ (errorId 8)) (withPeer hotPeer m4) ≡ just errorWaiting
sync-error-enters-wait = refl
sync-error-awaits-real-demotion : PS.step (PS.commitMonitorError tid₀) errorWaiting ≡ nothing
sync-error-awaits-real-demotion = refl
sync-wait-retains-status-and-duration : peerAt (ident 0) errorWaiting ≡ just hotPeer
sync-wait-retains-status-and-duration = refl
waitingMonitor : PS.State → PS.State
waitingMonitor s = record s { monitorPool = record (PS.monitorPool s)
  { phase = Pool.cancelPending tid₀; snapshot = tid₀ ∷ []; remaining = tid₀ ∷ [] } }
errorCancelled errorUnwound : PS.State
errorCancelled = after (PS.deliverBlockedMonitorCancellation (errorId 9)) (waitingMonitor errorWaiting)
errorUnwound = after (PS.monitorBodyUnwound tid₀) errorCancelled
ordinary-cancel-cannot-invent-masked-wait-window : PS.step (PS.deliverMonitorCancellation (errorId 9)) (waitingMonitor errorWaiting) ≡ nothing
ordinary-cancel-cannot-invent-masked-wait-window = refl
blocked-wait-is-interruptible : PS.step (PS.deliverBlockedMonitorCancellation (errorId 9)) (waitingMonitor errorWaiting) ≡ just errorCancelled
blocked-wait-is-interruptible = refl
wait-cancellation-unwinds : PS.step (PS.monitorBodyUnwound tid₀) errorCancelled ≡ just errorUnwound
wait-cancellation-unwinds = refl
async-wait-cancel-does-not-force-cold : peerAt (ident 0) errorUnwound ≡ just (record hotPeer { monitorStarted = false })
async-wait-cancel-does-not-force-cold = refl
cancelled-physical-thread-cannot-poll : PS.step (PS.run (GP.run (Sub.pollPeer (ident 0) monitorWorker))) errorUnwound ≡ nothing
cancelled-physical-thread-cannot-poll = refl
cancelled-monitor-no-queue : Pool.completions (PS.monitorPool errorUnwound) ≡ []
cancelled-monitor-no-queue = refl
withDemotedCM : PS.State → PS.State
withDemotedCM s = record s { governor = GP.setCM
  (record (PS.cm s) { core = Inbound.replaceWorld (CM.core (PS.cm s))
    (record (PS.shared s) { cm = record (S.cm (PS.shared s))
      { entries = put (ident 0) (S.inboundIdle key₀ O.child (ident 0) duplex) (S.entries (S.cm (PS.shared s))) } }) })
  (PS.governor s) }
errorCommitted errorFinished : PS.State
errorCommitted = after (PS.commitMonitorError tid₀) (withDemotedCM errorWaiting)
errorFinished = after (PS.finishMonitorError tid₀) errorCommitted
sync-error-commits-after-demotion : PS.step (PS.commitMonitorError tid₀) (withDemotedCM errorWaiting) ≡ just errorCommitted
sync-error-commits-after-demotion = refl
sync-error-commit-writes-cold : peerAt (ident 0) errorCommitted ≡ just (record hotPeer { status = Peer.peerCold })
sync-error-commit-writes-cold = refl
sync-error-finishes-separately : PS.step (PS.finishMonitorError tid₀) errorCommitted ≡ just errorFinished
sync-error-finishes-separately = refl
sync-error-finish-clears-duration : peerAt (ident 0) errorFinished ≡ just
  (record hotPeer { status = Peer.peerCold; promotedAt = nothing; monitorStarted = false })
sync-error-finish-clears-duration = refl

-- Conditional active followup: its captured release already committed idle or
-- pruning changes. Cancelling the physical thread detaches that exact caller.
withRelease : CM.Configuration → PS.State
withRelease c = PS.setMachine (record (PS.machine (withPeer hotPeer m4))
  { world = record (Sub.world (PS.machine (withPeer hotPeer m4)))
      { cm = record c { releasing = (monitorWorker , R.frame key₀
          (R.prune (Release.victim ∷ []) Release.pruneResult) false) ∷ [] } }
  ; monitors = ((ident 0) , J.frame (G.job G.close L.peerAddr (just (ident 0)))
      monitorWorker monitorWorker (ident 0) (ident 0) J.awaitRelease) ∷ [] }) (withPeer hotPeer m4)
releaseCancelling releaseUnwound : PS.State
releaseCancelling = after (PS.deliverMonitorCancellation (errorId 9)) (waitingMonitor (withRelease Release.p2))
releaseUnwound = after (PS.monitorBodyUnwound tid₀) releaseCancelling
active-release-cancelled : PS.step (PS.deliverMonitorCancellation (errorId 9)) (waitingMonitor (withRelease Release.p2)) ≡ just releaseCancelling
active-release-cancelled = refl
active-release-retains-committed-core : CM.core (PS.cm releaseCancelling) ≡ CM.core Release.p2
active-release-retains-committed-core = refl
active-release-caller-detached : CM.releasing (PS.cm releaseCancelling) ≡ []
active-release-caller-detached = refl
active-followup-detached : Sub.monitors (PS.machine releaseCancelling) ≡ []
active-followup-detached = refl
active-release-unwinds : PS.step (PS.monitorBodyUnwound tid₀) releaseCancelling ≡ just releaseUnwound
active-release-unwinds = refl
active-release-no-governor-completion : Sub.completions (PS.machine releaseUnwound) ≡ []
active-release-no-governor-completion = refl
active-release-preserves-status-control-duration : peerAt (ident 0) releaseUnwound ≡ just (record hotPeer { monitorStarted = false })
active-release-preserves-status-control-duration = refl
active-release-cannot-resume : PS.step (PS.run (GP.run (Sub.core (CM.release monitorWorker R.requestCancellation)))) releaseUnwound ≡ nothing
active-release-cannot-resume = refl

interruptedCall : PS.State → Maybe Cancel.Call
interruptedCall s with lookup tid₀ (PS.monitors s)
... | nothing = nothing
... | just t with PS.interrupted t
...   | nothing = nothing
...   | just f = just (Cancel.original f)
active-release-keeps-unsent-tail : interruptedCall releaseCancelling ≡ just
  (Cancel.releasing (R.frame key₀ (R.prune (Release.victim ∷ []) Release.pruneResult) false))
active-release-keeps-unsent-tail = refl

-- Actual initialized outer unwinding with an empty governor/PSA pool. Governor
-- local-body exit waits for its own pool close; provider joins precede the PSA
-- snapshot. This certifies only the scopes represented here, excluding SI4/5.
scopeThreads0 : Scope.Actor → Scope.ThreadPhase
scopeThreads0 _ = Scope.running
scopeThreads1 : Scope.Actor → Scope.ThreadPhase
scopeThreads1 = Scope.setPhase Scope.churn Scope.cancelRequested scopeThreads0
scopeThreads2 : Scope.Actor → Scope.ThreadPhase
scopeThreads2 = Scope.setPhase Scope.churn Scope.cancelDelivered scopeThreads1
scopeThreads3 : Scope.Actor → Scope.ThreadPhase
scopeThreads3 = Scope.setPhase Scope.churn Scope.bodyExited scopeThreads2
scopeThreads4 : Scope.Actor → Scope.ThreadPhase
scopeThreads4 = Scope.setPhase Scope.churn Scope.resultAvailable scopeThreads3
scopeThreads5 : Scope.Actor → Scope.ThreadPhase
scopeThreads5 = Scope.setPhase Scope.churn Scope.joined scopeThreads4
scopeThreads6 : Scope.Actor → Scope.ThreadPhase
scopeThreads6 = Scope.setPhase Scope.governor Scope.cancelRequested scopeThreads5
scopeThreads7 : Scope.Actor → Scope.ThreadPhase
scopeThreads7 = Scope.setPhase Scope.governor Scope.cancelDelivered scopeThreads6
scopeThreads8 : Scope.Actor → Scope.ThreadPhase
scopeThreads8 = Scope.setPhase Scope.governor Scope.bodyExited scopeThreads7
scopeThreads9 : Scope.Actor → Scope.ThreadPhase
scopeThreads9 = Scope.setPhase Scope.governor Scope.resultAvailable scopeThreads8
scopeThreads10 : Scope.Actor → Scope.ThreadPhase
scopeThreads10 = Scope.setPhase Scope.governor Scope.joined scopeThreads9
scopeThreads11 : Scope.Actor → Scope.ThreadPhase
scopeThreads11 = Scope.setPhase Scope.localRoot Scope.cancelRequested scopeThreads10
scopeThreads12 : Scope.Actor → Scope.ThreadPhase
scopeThreads12 = Scope.setPhase Scope.localRoot Scope.cancelDelivered scopeThreads11
scopeThreads13 : Scope.Actor → Scope.ThreadPhase
scopeThreads13 = Scope.setPhase Scope.localRoot Scope.bodyExited scopeThreads12
scopeThreads14 : Scope.Actor → Scope.ThreadPhase
scopeThreads14 = Scope.setPhase Scope.localRoot Scope.resultAvailable scopeThreads13
scopeThreads15 : Scope.Actor → Scope.ThreadPhase
scopeThreads15 = Scope.setPhase Scope.localRoot Scope.joined scopeThreads14
scopeThreads16 : Scope.Actor → Scope.ThreadPhase
scopeThreads16 = Scope.setPhase Scope.ledger Scope.cancelRequested scopeThreads15
scopeThreads17 : Scope.Actor → Scope.ThreadPhase
scopeThreads17 = Scope.setPhase Scope.ledger Scope.cancelDelivered scopeThreads16
scopeThreads18 : Scope.Actor → Scope.ThreadPhase
scopeThreads18 = Scope.setPhase Scope.ledger Scope.bodyExited scopeThreads17
scopeThreads19 : Scope.Actor → Scope.ThreadPhase
scopeThreads19 = Scope.setPhase Scope.ledger Scope.resultAvailable scopeThreads18
scopeThreads20 : Scope.Actor → Scope.ThreadPhase
scopeThreads20 = Scope.setPhase Scope.ledger Scope.joined scopeThreads19

outer1 : PS.State
outer1 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.openPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads0 (Scope.closing Scope.churn) false)
outer-step1 : PS.step (PS.scope Scope.beginUnwind) p₀ ≡ just outer1
outer-step1 = refl
outer2 : PS.State
outer2 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.openPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads1 (Scope.closing Scope.churn) true)
outer-step2 : PS.step (PS.scope Scope.requestCancel) outer1 ≡ just outer2
outer-step2 = refl
outer3 : PS.State
outer3 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.openPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads2 (Scope.closing Scope.churn) true)
outer-step3 : PS.step (PS.scope Scope.deliverCancel) outer2 ≡ just outer3
outer-step3 = refl
outer4 : PS.State
outer4 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.openPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads3 (Scope.closing Scope.churn) true)
outer-step4 : PS.step (PS.scope (Scope.bodyExit Scope.churn)) outer3 ≡ just outer4
outer-step4 = refl
outer5 : PS.State
outer5 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.openPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads4 (Scope.closing Scope.churn) true)
outer-step5 : PS.step (PS.scope (Scope.publishResult Scope.churn)) outer4 ≡ just outer5
outer-step5 = refl
outer6 : PS.State
outer6 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.openPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads5 (Scope.closing Scope.governor) false)
outer-step6 : PS.step (PS.scope Scope.join) outer5 ≡ just outer6
outer-step6 = refl
outer7 : PS.State
outer7 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.openPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads6 (Scope.closing Scope.governor) true)
outer-step7 : PS.step (PS.scope Scope.requestCancel) outer6 ≡ just outer7
outer-step7 = refl
outer8 : PS.State
outer8 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.openPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
outer-step8 : PS.step (PS.scope Scope.deliverCancel) outer7 ≡ just outer8
outer-step8 = refl
outer9 : PS.State
outer9 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closing } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
outer-step9 : PS.step (PS.run (GP.beginClose [])) outer8 ≡ just outer9
outer-step9 = refl
outer10 : PS.State
outer10 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads7 (Scope.closing Scope.governor) true)
outer-step10 : PS.step (PS.run GP.finishClose) outer9 ≡ just outer10
outer-step10 = refl
outer11 : PS.State
outer11 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads8 (Scope.closing Scope.governor) true)
outer-step11 : PS.step (PS.scope (Scope.bodyExit Scope.governor)) outer10 ≡ just outer11
outer-step11 = refl
outer12 : PS.State
outer12 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads9 (Scope.closing Scope.governor) true)
outer-step12 : PS.step (PS.scope (Scope.publishResult Scope.governor)) outer11 ≡ just outer12
outer-step12 = refl
outer13 : PS.State
outer13 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads10 (Scope.closing Scope.localRoot) false)
outer-step13 : PS.step (PS.scope Scope.join) outer12 ≡ just outer13
outer-step13 = refl
outer14 : PS.State
outer14 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads11 (Scope.closing Scope.localRoot) true)
outer-step14 : PS.step (PS.scope Scope.requestCancel) outer13 ≡ just outer14
outer-step14 = refl
outer15 : PS.State
outer15 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads12 (Scope.closing Scope.localRoot) true)
outer-step15 : PS.step (PS.scope Scope.deliverCancel) outer14 ≡ just outer15
outer-step15 = refl
outer16 : PS.State
outer16 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads13 (Scope.closing Scope.localRoot) true)
outer-step16 : PS.step (PS.scope (Scope.bodyExit Scope.localRoot)) outer15 ≡ just outer16
outer-step16 = refl
outer17 : PS.State
outer17 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads14 (Scope.closing Scope.localRoot) true)
outer-step17 : PS.step (PS.scope (Scope.publishResult Scope.localRoot)) outer16 ≡ just outer17
outer-step17 = refl
outer18 : PS.State
outer18 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads15 (Scope.closing Scope.ledger) false)
outer-step18 : PS.step (PS.scope Scope.join) outer17 ≡ just outer18
outer-step18 = refl
outer19 : PS.State
outer19 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads16 (Scope.closing Scope.ledger) true)
outer-step19 : PS.step (PS.scope Scope.requestCancel) outer18 ≡ just outer19
outer-step19 = refl
outer20 : PS.State
outer20 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads17 (Scope.closing Scope.ledger) true)
outer-step20 : PS.step (PS.scope Scope.deliverCancel) outer19 ≡ just outer20
outer-step20 = refl
outer21 : PS.State
outer21 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads18 (Scope.closing Scope.ledger) true)
outer-step21 : PS.step (PS.scope (Scope.bodyExit Scope.ledger)) outer20 ≡ just outer21
outer-step21 = refl
outer22 : PS.State
outer22 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads19 (Scope.closing Scope.ledger) true)
outer-step22 : PS.step (PS.scope (Scope.publishResult Scope.ledger)) outer21 ≡ just outer22
outer-step22 = refl
outer23 : PS.State
outer23 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads20 Scope.readyToFinish false)
outer-step23 : PS.step (PS.scope Scope.join) outer22 ≡ just outer23
outer-step23 = refl
outer24 : PS.State
outer24 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.openPool }) (Scope.scopes scopeThreads20 Scope.finishedScope false)
outer-step24 : PS.step (PS.scope Scope.finishClose) outer23 ≡ just outer24
outer-step24 = refl
outer25 : PS.State
outer25 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.closing }) (Scope.scopes scopeThreads20 Scope.finishedScope false)
outer-step25 : PS.step (PS.beginMonitorClose []) outer24 ≡ just outer25
outer-step25 = refl
outer26 : PS.State
outer26 = PS.supervising (record (GP.initial (CM.initial F.start) L.settings)
  { pool = record GP.Pool.initial { phase = GP.Pool.closedPool } }) []
  (record Pool.initial { phase = Pool.closedPool }) (Scope.scopes scopeThreads20 Scope.finishedScope false)
outer-step26 : PS.step (PS.finishMonitorClose) outer25 ≡ just outer26
outer-step26 = refl
outerActions : List PS.Action
outerActions = (PS.scope Scope.beginUnwind) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.scope (Scope.bodyExit Scope.churn)) ∷ (PS.scope (Scope.publishResult Scope.churn)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.run (GP.beginClose [])) ∷ (PS.run GP.finishClose) ∷ (PS.scope (Scope.bodyExit Scope.governor)) ∷ (PS.scope (Scope.publishResult Scope.governor)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.scope (Scope.bodyExit Scope.localRoot)) ∷ (PS.scope (Scope.publishResult Scope.localRoot)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.requestCancel) ∷ (PS.scope Scope.deliverCancel) ∷ (PS.scope (Scope.bodyExit Scope.ledger)) ∷ (PS.scope (Scope.publishResult Scope.ledger)) ∷ (PS.scope Scope.join) ∷ (PS.scope Scope.finishClose) ∷ (PS.beginMonitorClose []) ∷ (PS.finishMonitorClose) ∷ []
-- Keep checked execution evidence opaque to downstream certificate reduction.
abstract
  initialized-outer-close : PS.Executes p₀ outerActions outer26
  initialized-outer-close = PS.next outer-step1 (PS.next outer-step2 (PS.next outer-step3 (PS.next outer-step4 (PS.next outer-step5 (PS.next outer-step6 (PS.next outer-step7 (PS.next outer-step8 (PS.next outer-step9 (PS.next outer-step10 (PS.next outer-step11 (PS.next outer-step12 (PS.next outer-step13 (PS.next outer-step14 (PS.next outer-step15 (PS.next outer-step16 (PS.next outer-step17 (PS.next outer-step18 (PS.next outer-step19 (PS.next outer-step20 (PS.next outer-step21 (PS.next outer-step22 (PS.next outer-step23 (PS.next outer-step24 (PS.next outer-step25 (PS.next outer-step26 (PS.done))))))))))))))))))))))))))
governor-async-body-cannot-outrun-own-pool : PS.step (PS.scope (Scope.bodyExit Scope.governor)) outer8 ≡ nothing
governor-async-body-cannot-outrun-own-pool = refl
closed-governor-pool-does-not-close-psa-scope : PS.step (PS.beginMonitorClose []) outer10 ≡ nothing
closed-governor-pool-does-not-close-psa-scope = refl
governor-join-precedes-providers : Scope.cursor (PS.scopes outer13) ≡ Scope.closing Scope.localRoot
governor-join-precedes-providers = refl
local-root-join-precedes-ledger : Scope.cursor (PS.scopes outer18) ≡ Scope.closing Scope.ledger
local-root-join-precedes-ledger = refl
all-providers-joined-before-psa-snapshot : Scope.closed (PS.scopes outer25) ≡ true
all-providers-joined-before-psa-snapshot = refl
initialized-outer-psa-pool-closed : Pool.phase (PS.monitorPool outer26) ≡ Pool.closedPool
initialized-outer-psa-pool-closed = refl

-- A Cold observation inside a followup is not yet return from the physical
-- monitor loop. Finish/remove that operation, then poll the loop again.
activeColdFollowup : PS.State
activeColdFollowup = PS.setMachine (record (PS.machine (withPeer coldPeer m4))
  { monitors = ((ident 0) , J.frame (G.job G.close L.peerAddr (just (ident 0)))
      monitorWorker monitorWorker (ident 0) (ident 0) (J.awaitCold G.succeeded)) ∷ [] })
  (withPeer coldPeer m4)
followupPolled followupComplete followupRemoved loopReturned : PS.State
followupPolled = after (PS.run (GP.run (Sub.pollPeer (ident 0) monitorWorker))) activeColdFollowup
followupComplete = after (PS.run (GP.run (Sub.monitorStep (ident 0) J.observeCold))) followupPolled
followupRemoved = after (PS.run (GP.run (Sub.monitorFinished (ident 0)))) followupComplete
loopReturned = after (PS.run (GP.run (Sub.pollPeer (ident 0) monitorWorker))) followupRemoved
followup-cold-observation : PS.step (PS.run (GP.run (Sub.pollPeer (ident 0) monitorWorker))) activeColdFollowup ≡ just followupPolled
followup-cold-observation = refl
active-followup-prevents-physical-exit : PS.step (PS.finishMonitor tid₀) followupPolled ≡ nothing
active-followup-prevents-physical-exit = refl
active-followup-retains-duration : peerAt (ident 0) followupPolled ≡ just coldPeer
active-followup-retains-duration = refl
followup-observes-cold : PS.step (PS.run (GP.run (Sub.monitorStep (ident 0) J.observeCold))) followupPolled ≡ just followupComplete
followup-observes-cold = refl
followup-removed-before-loop-return : PS.step (PS.run (GP.run (Sub.monitorFinished (ident 0)))) followupComplete ≡ just followupRemoved
followup-removed-before-loop-return = refl
loop-poll-after-followup : PS.step (PS.run (GP.run (Sub.pollPeer (ident 0) monitorWorker))) followupRemoved ≡ just loopReturned
loop-poll-after-followup = refl
physical-exit-after-followup-and-loop-return : PS.step (PS.finishMonitor tid₀) loopReturned ≡ just (after (PS.finishMonitor tid₀) loopReturned)
physical-exit-after-followup-and-loop-return = refl

-- Scope failure is explicit and distinct from delivered cancellation.
no-governor-close-before-unwind : PS.step (PS.run (GP.beginClose [])) p₀ ≡ nothing
no-governor-close-before-unwind = refl
governorFailed : PS.State
governorFailed = after (PS.scope (Scope.beginFailure Scope.governor)) p₀
independent-governor-failure : PS.step (PS.scope (Scope.beginFailure Scope.governor)) p₀ ≡ just governorFailed
independent-governor-failure = refl
failure-enables-own-pool-close : PS.step (PS.run (GP.beginClose [])) governorFailed ≡ just
  (after (PS.run (GP.beginClose [])) governorFailed)
failure-enables-own-pool-close = refl


-- Conditional malformed followup: the captured physical worker cannot borrow
-- an operation whose caller belongs to another thread, even when peer IDs match.
wrongFollowupOwner : PS.State
wrongFollowupOwner = PS.setMachine (record (PS.machine activeColdFollowup)
  { monitors = ((ident 0) , J.frame (G.job G.close L.peerAddr (just (ident 0)))
      (ident 99) (ident 99) (ident 0) (ident 0) (J.awaitCold G.succeeded)) ∷ [] }) activeColdFollowup
forged-followup-poll-refused : PS.step (PS.run (GP.run (Sub.pollPeer (ident 0) monitorWorker))) wrongFollowupOwner ≡ nothing
forged-followup-poll-refused = refl
forged-followup-step-refused : PS.step (PS.run (GP.run (Sub.monitorStep (ident 0) J.observeCold))) wrongFollowupOwner ≡ nothing
forged-followup-step-refused = refl

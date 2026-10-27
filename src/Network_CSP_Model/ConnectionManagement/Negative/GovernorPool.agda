{-# OPTIONS --guardedness #-}

-- Source-coupled governor-pool controls. The initialized prefix below is a real
-- execution. Later matched release, completion and handoff snapshots are local
-- controls, not new source-reachability or whole-node supervision claims.
module ConnectionManagement.Negative.GovernorPool where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.GovernorPool as Governor
import ConnectionManagement.Properties.GovernorPool as Certificates
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.State as S
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.CSP.OutboundAdmission as O
import ConnectionManagement.CSP.OutboundReleaseScenarios as Release
import ConnectionManagement.CSP.Fixtures as F
open import ConnectionManagement.Scenarios.Admission using (key₀)

classify : ErrorId → Bool
classify (errorId 7) = true
classify _ = false
module GP = Governor classify
module Pool = GP.Pool
module Cert = Certificates classify

j₀ : JobId
j₀ = ident 0
work : G.Job
work = G.job G.establish L.peerAddr nothing
runningPool : Pool.State
runningPool = Pool.poolState ((j₀ , Pool.bodyRunning) ∷ [])
  (j₀ ∷ []) nothing Pool.openPool [] [] [] []
gapPool : Pool.State
gapPool = Pool.poolState ((j₀ , Pool.bodyRunning) ∷ [])
  [] (just j₀) Pool.openPool [] [] [] []
live : Sub.Configuration → Pool.State → GP.State
live c p = GP.supervised (GP.Production.initial c) p [] []
g₀ : GP.State
g₀ = GP.initial (CM.initial F.start) L.settings
g1 : GP.State
g1 = live L.c1 Pool.initial
g2 : GP.State
g2 = live L.c2 Pool.initial
g3 : GP.State
g3 = live L.c3 Pool.initial
g4 : GP.State
g4 = live L.c4 Pool.initial
g5 : GP.State
g5 = live L.c5 Pool.initial
g6 : GP.State
g6 = live L.c6 Pool.initial
g7 : GP.State
g7 = live L.c7 Pool.initial
g8 : GP.State
g8 = live L.c8 gapPool
g9 : GP.State
g9 = live L.c9 runningPool
g10 : GP.State
g10 = live L.c10 runningPool
g11 : GP.State
g11 = live L.c11 runningPool
g12 : GP.State
g12 = live L.c12 runningPool
g13 : GP.State
g13 = live L.c13 runningPool
g14 : GP.State
g14 = live L.c14 runningPool
g15 : GP.State
g15 = live L.c15 runningPool
g16 : GP.State
g16 = live L.c16 runningPool
g17 : GP.State
g17 = live L.c17 runningPool
g18 : GP.State
g18 = live L.c18 runningPool
g19 : GP.State
g19 = record (live L.c19 runningPool) { regions = (L.caller , Cancel.forkedBeforeHandoff) ∷ [] }
initialized-step1 : GP.step (GP.run L.a1) g₀ ≡ just g1
initialized-step1 = refl
initialized-step2 : GP.step (GP.run L.a2) g1 ≡ just g2
initialized-step2 = refl
initialized-step3 : GP.step (GP.run L.a3) g2 ≡ just g3
initialized-step3 = refl
initialized-step4 : GP.step (GP.run L.a4) g3 ≡ just g4
initialized-step4 = refl
initialized-step5 : GP.step (GP.run L.a5) g4 ≡ just g5
initialized-step5 = refl
initialized-step6 : GP.step (GP.run L.a6) g5 ≡ just g6
initialized-step6 = refl
initialized-step7 : GP.step (GP.run L.a7) g6 ≡ just g7
initialized-step7 = refl
initialized-step8 : GP.step (GP.run L.a8) g7 ≡ just g8
initialized-step8 = refl
initialized-step9 : GP.step (GP.run L.a9) g8 ≡ just g9
initialized-step9 = refl
initialized-step10 : GP.step (GP.run L.a10) g9 ≡ just g10
initialized-step10 = refl
initialized-step11 : GP.step (GP.run L.a11) g10 ≡ just g11
initialized-step11 = refl
initialized-step12 : GP.step (GP.run L.a12) g11 ≡ just g12
initialized-step12 = refl
initialized-step13 : GP.step (GP.run L.a13) g12 ≡ just g13
initialized-step13 = refl
initialized-step14 : GP.step (GP.run L.a14) g13 ≡ just g14
initialized-step14 = refl
initialized-step15 : GP.step (GP.run L.a15) g14 ≡ just g15
initialized-step15 = refl
initialized-step16 : GP.step (GP.run L.a16) g15 ≡ just g16
initialized-step16 = refl
initialized-step17 : GP.step (GP.run L.a17) g16 ≡ just g17
initialized-step17 = refl
initialized-step18 : GP.step (GP.run L.a18) g17 ≡ just g18
initialized-step18 = refl
initialized-step19 : GP.step (GP.run L.a19) g18 ≡ just g19
initialized-step19 = refl

-- A successful-step assertion accompanies each computed local snapshot; the
-- projection controls then check concrete effects, rather than only success.
after : GP.Action → GP.State → GP.State
after a s with GP.step a s
... | nothing = s
... | just s′ = s′
closingAt : GP.State → GP.State
closingAt s = record s { pool = record (GP.pool s)
  { phase = Pool.closing; snapshot = j₀ ∷ []; remaining = j₀ ∷ [] } }
waitingAt : GP.State → GP.State
waitingAt s = record (closingAt s) { pool = record (GP.pool (closingAt s))
  { phase = Pool.cancelPending j₀ } }

fork-registration-gap-blocks-close : GP.step (GP.beginClose (j₀ ∷ [])) g8 ≡ nothing
fork-registration-gap-blocks-close = refl
registered-close : GP.step (GP.beginClose (j₀ ∷ [])) g13 ≡ just (closingAt g13)
registered-close = refl
select-current-handle : GP.step GP.requestCancel (closingAt g13) ≡ just (waitingAt g13)
select-current-handle = refl
ordinary-open-is-masked : GP.step (GP.deliverCancellation (errorId 9)) (waitingAt g13) ≡ nothing
ordinary-open-is-masked = refl

-- Before the socket bracket owns a resource, cancellation leaves the allocated
-- reservation intact. Explicit blocked-open interruptibility permits delivery.
openFrame : Cancel.Frame
openFrame = Cancel.cancellation L.caller (errorId 9)
  (Cancel.acquiring (A.frame O.req (A.openSocket (ident 0) (ident 0))))
  (Cancel.finished Cancel.abandoned)
openCancelled : GP.State
openCancelled = record (GP.setCM (record (GP.cm g13) { acquiring = [] }) (waitingAt g13))
  { pool = record (GP.pool (waitingAt g13))
    { handles = (j₀ , Pool.bodyUnwinding) ∷ []; phase = Pool.joinPending j₀ }
  ; unwinding = (j₀ , openFrame) ∷ [] }
blocked-open-delivered : GP.step (GP.deliverOpenCancellation (errorId 9)) (waitingAt g13) ≡ just openCancelled
blocked-open-delivered = refl
open-keeps-reservation : Inbound.world (CM.core (GP.cm openCancelled)) ≡ O.promised
open-keeps-reservation = refl
open-does-not-return : CM.acquired (GP.cm openCancelled) ≡ []
open-does-not-return = refl
cancelled-caller-cannot-open : GP.step (GP.run L.a14) openCancelled ≡ nothing
cancelled-caller-cannot-open = refl
cancelled-job-cannot-resume : GP.step (GP.run (Sub.jobStep j₀ J.collectAcquire)) openCancelled ≡ nothing
cancelled-job-cannot-resume = refl
unwindOpen deregOpen asyncOpen joinedOpen closedOpen : GP.State
unwindOpen = record openCancelled { pool = record (GP.pool openCancelled)
  { handles = (j₀ , Pool.deregisterPending Pool.cancelledExit) ∷ [] } }
deregOpen = after (GP.deregisterCancelled j₀) unwindOpen
asyncOpen = after (GP.publishAsyncResult j₀) deregOpen
joinedOpen = after GP.join asyncOpen
closedOpen = after GP.finishClose joinedOpen
open-body-unwinds : GP.step (GP.bodyUnwound j₀) openCancelled ≡ just unwindOpen
open-body-unwinds = refl
cancelled-deregisters : GP.step (GP.deregisterCancelled j₀) unwindOpen ≡ just deregOpen
cancelled-deregisters = refl
cancelled-async-result : GP.step (GP.publishAsyncResult j₀) deregOpen ≡ just asyncOpen
cancelled-async-result = refl
captured-handle-joins : GP.step GP.join asyncOpen ≡ just joinedOpen
captured-handle-joins = refl
close-after-join : GP.step GP.finishClose joinedOpen ≡ just closedOpen
close-after-join = refl
cancelled-dereg-no-source-queue : Sub.completions (GP.machine deregOpen) ≡ []
cancelled-dereg-no-source-queue = refl
cancelled-dereg-no-ledger-queue : Pool.completions (GP.pool deregOpen) ≡ []
cancelled-dereg-no-ledger-queue = refl
cancelled-removes-source-registration : Sub.pool (GP.machine deregOpen) ≡ []
cancelled-removes-source-registration = refl
closed-phase : Pool.phase (GP.pool closedOpen) ≡ Pool.closedPool
closed-phase = refl

prefix : List GP.Action
prefix = GP.run L.a1 ∷ GP.run L.a2 ∷ GP.run L.a3 ∷ GP.run L.a4 ∷ GP.run L.a5 ∷ GP.run L.a6 ∷ GP.run L.a7 ∷ GP.run L.a8 ∷ GP.run L.a9 ∷ GP.run L.a10 ∷ GP.run L.a11 ∷ GP.run L.a12 ∷ GP.run L.a13 ∷ []
prefix-path : GP.Executes g₀ prefix g13
prefix-path = GP.next initialized-step1 (GP.next initialized-step2 (GP.next initialized-step3 (GP.next initialized-step4 (GP.next initialized-step5 (GP.next initialized-step6 (GP.next initialized-step7 (GP.next initialized-step8 (GP.next initialized-step9 (GP.next initialized-step10 (GP.next initialized-step11 (GP.next initialized-step12 (GP.next initialized-step13 (GP.done)))))))))))))
closeActions : List GP.Action
closeActions = GP.beginClose (j₀ ∷ []) ∷ GP.requestCancel ∷
  GP.deliverOpenCancellation (errorId 9) ∷ GP.bodyUnwound j₀ ∷
  GP.deregisterCancelled j₀ ∷ GP.publishAsyncResult j₀ ∷ GP.join ∷ GP.finishClose ∷ []
close-path : GP.Executes g13 closeActions closedOpen
close-path = GP.next registered-close (GP.next select-current-handle
  (GP.next blocked-open-delivered (GP.next open-body-unwinds
  (GP.next cancelled-deregisters (GP.next cancelled-async-result
  (GP.next captured-handle-joins (GP.next close-after-join GP.done)))))))

-- Apply the generic coupled projection/certificate to this initialized run.
open import Data.List using (_++_)
append : ∀ {s as t bs u} → GP.Executes s as t → GP.Executes t bs u → GP.Executes s (as ++ bs) u
append GP.done right = right
append (GP.next eq left) right = GP.next eq (append left right)
initialized-close : GP.Executes g₀ (prefix ++ closeActions) closedOpen
initialized-close = append prefix-path close-path
initialized-close-terminal : ∀ j → j ∈ Pool.snapshot (GP.pool closedOpen) → Cert.Close.Terminal (GP.pool closedOpen) j
initialized-close-terminal = Cert.from-initial initialized-close closed-phase

-- Once acquired, the actual bracket writers close the captured socket and
-- remove the captured reservation, with the caller frame already detached.
bracketCancelled socketClosed reservationRemoved bracketDone : GP.State
bracketCancelled = after (GP.deliverCancellation (errorId 9)) (waitingAt g14)
socketClosed = after (GP.cleanup j₀ Cancel.closeSocket) bracketCancelled
reservationRemoved = after (GP.cleanup j₀ Cancel.removeReservation) socketClosed
bracketDone = after (GP.cleanup j₀ Cancel.readCounters) reservationRemoved
bracket-delivery : GP.step (GP.deliverCancellation (errorId 9)) (waitingAt g14) ≡ just bracketCancelled
bracket-delivery = refl
bracket-close : GP.step (GP.cleanup j₀ Cancel.closeSocket) bracketCancelled ≡ just socketClosed
bracket-close = refl
bracket-remove : GP.step (GP.cleanup j₀ Cancel.removeReservation) socketClosed ≡ just reservationRemoved
bracket-remove = refl
bracket-count : GP.step (GP.cleanup j₀ Cancel.readCounters) reservationRemoved ≡ just bracketDone
bracket-count = refl
closed-real-socket : lookup O.sock (S.sockets (Inbound.world (CM.core (GP.cm socketClosed)))) ≡ just S.closed
closed-real-socket = refl
removed-real-reservation : S.mapCell (S.cm (Inbound.world (CM.core (GP.cm reservationRemoved)))) ≡ S.full []
removed-real-reservation = refl
terminated-real-entry : lookup (ident 0) (S.entries (S.cm (Inbound.world (CM.core (GP.cm reservationRemoved))))) ≡ just (S.terminated nothing)
terminated-real-entry = refl
cleanup-keeps-caller-detached : CM.acquiring (GP.cm bracketDone) ≡ []
cleanup-keeps-caller-detached = refl
cleanup-completes-before-dereg : lookup j₀ (Pool.handles (GP.pool bracketDone)) ≡ just Pool.bodyUnwinding
cleanup-completes-before-dereg = refl
cleanup-finish : Maybe Cancel.PC
cleanup-finish with lookup j₀ (GP.unwinding bracketDone)
... | nothing = nothing
... | just f = just (Cancel.pc f)
cleanup-finished : cleanup-finish ≡ just (Cancel.finished Cancel.cleanupComplete)
cleanup-finished = refl

-- Protection is recorded by the actual ordinary exception entry, not inferred
-- from an exception identifier at cancellation delivery time.
protected : GP.State
protected = after (GP.run (Sub.core (CM.acquire L.caller (A.failIO (errorId 8))))) g14
source-failure-enters-cleanup : GP.step (GP.run (Sub.core (CM.acquire L.caller (A.failIO (errorId 8))))) g14 ≡ just protected
source-failure-enters-cleanup = refl
protected-region : GP.region L.caller protected ≡ Cancel.protectedCleanup
protected-region = refl
protected-cleanup-rejects-delivery : GP.step (GP.deliverCancellation (errorId 9)) (waitingAt protected) ≡ nothing
protected-cleanup-rejects-delivery = refl
protected-cleanup-rejects-open-override : GP.step (GP.deliverOpenCancellation (errorId 9)) (waitingAt protected) ≡ nothing
protected-cleanup-rejects-open-override = refl
owner-paused-other-inputs-live : GP.step (GP.run Sub.finishLaunch) bracketCancelled ≡ nothing
owner-paused-other-inputs-live = refl
external-target-write : GP.step (GP.run (Sub.setTargets (G.targets 2 1 1))) bracketCancelled ≡ just
  (record bracketCancelled { source = record (GP.source bracketCancelled)
    { machine = record (GP.machine bracketCancelled) { targetInput = G.targets 2 1 1 } } })
external-target-write = refl
otherCaller : WorkerId
otherCaller = ident 30
other-caller-can-begin : GP.step (GP.run (Sub.core (CM.beginAcquire otherCaller O.req))) bracketCancelled ≡ just
  (record (GP.setCM (record (GP.cm bracketCancelled)
    { acquiring = (otherCaller , A.frame O.req A.selecting) ∷ [] }) bracketCancelled)
    { regions = (otherCaller , Cancel.ordinary) ∷ [] })
other-caller-can-begin = refl

-- The source fork has happened, but ownership handoff is an explicit boundary.
handed : GP.State
handed = record g19 { regions = (L.caller , Cancel.ordinary) ∷ [] }
pre-handoff-cannot-commit : GP.step (GP.run L.a20) g19 ≡ nothing
pre-handoff-cannot-commit = refl
explicit-handoff : GP.step (GP.handoff L.caller) g19 ≡ just handed
explicit-handoff = refl
handoff-enables-commit : GP.step (GP.run L.a20) handed ≡ just
  (record (live L.c20 runningPool) { regions = (L.caller , Cancel.ordinary) ∷ [] })
handoff-enables-commit = refl
preHandoffCancel postHandoffCancel : GP.State
preHandoffCancel = after (GP.deliverCancellation (errorId 9)) (waitingAt g19)
postHandoffCancel = after (GP.deliverCancellation (errorId 9)) (waitingAt handed)
pre-handoff-delivery : GP.step (GP.deliverCancellation (errorId 9)) (waitingAt g19) ≡ just preHandoffCancel
pre-handoff-delivery = refl
post-handoff-delivery : GP.step (GP.deliverCancellation (errorId 9)) (waitingAt handed) ≡ just postHandoffCancel
post-handoff-delivery = refl
pre-handoff-selects-cleanup : lookup j₀ (GP.unwinding preHandoffCancel) ≡ just
  (Cancel.cancellation L.caller (errorId 9)
    (Cancel.acquiring (A.frame O.req (A.connectedCommit (ident 0) (ident 0) key₀)))
    (Cancel.cleaning (A.frame O.req (A.closeError (ident 0) (Cases.ioFailure (errorId 9))))))
pre-handoff-selects-cleanup = refl
post-handoff-leaves-handler-world : Inbound.world (CM.core (GP.cm postHandoffCancel)) ≡ O.forked
post-handoff-leaves-handler-world = refl
post-handoff-abandons-only-caller : lookup j₀ (GP.unwinding postHandoffCancel) ≡ just
  (Cancel.cancellation L.caller (errorId 9)
    (Cancel.acquiring (A.frame O.req (A.connectedCommit (ident 0) (ident 0) key₀)))
    (Cancel.finished Cancel.abandoned))
post-handoff-abandons-only-caller = refl

-- A close exception replaces cancellation. It cannot be certified as a normal
-- cancellation unwind; the captured replacement goes through actual PSA policy.
closeError : ErrorId → GP.State
closeError err = after (GP.cleanup j₀ (Cancel.closeFailed err)) bracketCancelled
recovered : ErrorId → GP.State
recovered err = after (GP.recoverCloseFailure j₀) (closeError err)
captured : ErrorId → GP.State
captured err = after (GP.run (Sub.jobStep j₀ J.collectAcquire)) (recovered err)
failedReturned failedQueued failedDeregistered : GP.State
failedReturned = after (GP.run (Sub.jobStep j₀ J.choosePeerPolicy)) (captured (errorId 8))
failedQueued = after (GP.run (Sub.enqueueCompletion j₀ 2)) failedReturned
failedDeregistered = after (GP.run (Sub.deregisterJob j₀)) failedQueued
ordinary-close-throws : GP.step (GP.cleanup j₀ (Cancel.closeFailed (errorId 8))) bracketCancelled ≡ just (closeError (errorId 8))
ordinary-close-throws = refl
close-failure-skips-removal : S.mapCell (S.cm (Inbound.world (CM.core (GP.cm (closeError (errorId 8)))))) ≡ S.mapCell (S.cm O.opened)
close-failure-skips-removal = refl
close-failure-uncertain-socket : lookup O.sock (S.sockets (Inbound.world (CM.core (GP.cm (closeError (errorId 8)))))) ≡ just (S.closeUncertain (errorId 8))
close-failure-uncertain-socket = refl
close-failure-cannot-claim-unwind : GP.step (GP.bodyUnwound j₀) (closeError (errorId 8)) ≡ nothing
close-failure-cannot-claim-unwind = refl
replacement-recovers : GP.step (GP.recoverCloseFailure j₀) (closeError (errorId 8)) ≡ just (recovered (errorId 8))
replacement-recovers = refl
recovery-restores-only-job-policy : lookup j₀ (Pool.handles (GP.pool (recovered (errorId 8)))) ≡ just Pool.bodyRunning
recovery-restores-only-job-policy = refl
replacement-real-return-cell : lookup L.caller (CM.acquired (GP.cm (recovered (errorId 8)))) ≡ just (Cases.raised (Cases.ioFailure (errorId 8)))
replacement-real-return-cell = refl
replacement-captured : GP.step (GP.run (Sub.jobStep j₀ J.collectAcquire)) (recovered (errorId 8)) ≡ just (captured (errorId 8))
replacement-captured = refl
replacement-node-refused : GP.step (GP.run (Sub.jobStep j₀ J.chooseNodePolicy)) (captured (errorId 8)) ≡ nothing
replacement-node-refused = refl
replacement-peer-returns-failure : GP.step (GP.run (Sub.jobStep j₀ J.choosePeerPolicy)) (captured (errorId 8)) ≡ just failedReturned
replacement-peer-returns-failure = refl
replacement-real-body : lookup j₀ (Pool.handles (GP.pool failedReturned)) ≡ just (Pool.bodyReturned (GP.body j₀ work G.failed))
replacement-real-body = refl
replacement-real-enqueue : GP.step (GP.run (Sub.enqueueCompletion j₀ 2)) failedReturned ≡ just failedQueued
replacement-real-enqueue = refl
replacement-real-source-queue : Sub.completions (GP.machine failedQueued) ≡ G.completion work G.failed 2 ∷ []
replacement-real-source-queue = refl
replacement-real-ledger-queue : Pool.completions (GP.pool failedQueued) ≡ GP.body j₀ work G.failed ∷ []
replacement-real-ledger-queue = refl
replacement-normal-dereg : GP.step (GP.run (Sub.deregisterJob j₀)) failedQueued ≡ just failedDeregistered
replacement-normal-dereg = refl
replacement-is-normal-exit : lookup j₀ (Pool.handles (GP.pool failedDeregistered)) ≡ just (Pool.deregistered Pool.normalExit)
replacement-is-normal-exit = refl
fatal-close-throws : GP.step (GP.cleanup j₀ (Cancel.closeFailed (errorId 7))) bracketCancelled ≡ just (closeError (errorId 7))
fatal-close-throws = refl
fatal-replacement-recovers : GP.step (GP.recoverCloseFailure j₀) (closeError (errorId 7)) ≡ just (recovered (errorId 7))
fatal-replacement-recovers = refl
fatal-replacement-captured : GP.step (GP.run (Sub.jobStep j₀ J.collectAcquire)) (recovered (errorId 7)) ≡ just (captured (errorId 7))
fatal-replacement-captured = refl
fatal-replacement-peer-refused : GP.step (GP.run (Sub.jobStep j₀ J.choosePeerPolicy)) (captured (errorId 7)) ≡ nothing
fatal-replacement-peer-refused = refl
fatal-replacement-node-allowed : GP.step (GP.run (Sub.jobStep j₀ J.chooseNodePolicy)) (captured (errorId 7)) ≡ just
  (after (GP.run (Sub.jobStep j₀ J.chooseNodePolicy)) (captured (errorId 7)))
fatal-replacement-node-allowed = refl

-- Matched normal-return snapshot: publication must carry the actual job return,
-- then deregistration changes both registries, without making Async terminal.
normalBefore normalReturned normalQueued normalDeregistered : GP.State
normalBefore = live L.c39 runningPool
normalReturned = live L.c40 (record runningPool
  { handles = (j₀ , Pool.bodyReturned (GP.body j₀ work (G.establishedOK (ident 0)))) ∷ [] })
normalQueued = live L.c41 (record runningPool
  { handles = (j₀ , Pool.deregisterPending Pool.normalExit) ∷ []
  ; completions = GP.body j₀ work (G.establishedOK (ident 0)) ∷ [] })
normalDeregistered = live L.c42 (record (GP.pool normalQueued)
  { handles = (j₀ , Pool.deregistered Pool.normalExit) ∷ []; registered = [] })
normal-return-coupled : GP.step (GP.run L.a40) normalBefore ≡ just normalReturned
normal-return-coupled = refl
normal-enqueue-coupled : GP.step (GP.run L.a41) normalReturned ≡ just normalQueued
normal-enqueue-coupled = refl
normal-dereg-coupled : GP.step (GP.run L.a42) normalQueued ≡ just normalDeregistered
normal-dereg-coupled = refl
no-enqueue-before-body-return : GP.step (GP.run L.a41) (live L.c40 runningPool) ≡ nothing
no-enqueue-before-body-return = refl
no-invented-body-outcome : GP.step (GP.run L.a41) (live L.c40 (record runningPool
  { handles = (j₀ , Pool.bodyReturned (GP.body j₀ work G.failed)) ∷ [] })) ≡ nothing
no-invented-body-outcome = refl
no-dereg-before-publication : GP.step (GP.run L.a42) normalReturned ≡ nothing
no-dereg-before-publication = refl
normal-dereg-not-terminal : lookup j₀ (Pool.handles (GP.pool normalDeregistered)) ≡ just (Pool.deregistered Pool.normalExit)
normal-dereg-not-terminal = refl

-- Release snapshots deliberately begin inside their committed transactions.
-- Abandoning the caller preserves idle/pruning writes and unsent cancellation
-- targets. This does not establish termination of the handler they reference.
releaseAt : CM.Configuration → GP.State
releaseAt c = live (record (Sub.initial c L.settings)
  { jobs = (j₀ , Sub.jobFrame (J.frame (G.job G.close L.peerAddr (just (ident 0)))
      Release.caller O.child O.sock (ident 0) J.awaitRelease) false false) ∷ []
  ; pool = j₀ ∷ [] }) runningPool
idleCancelled pruneCancelled : GP.State
idleCancelled = after (GP.deliverCancellation (errorId 9)) (waitingAt (releaseAt Release.t4))
pruneCancelled = after (GP.deliverCancellation (errorId 9)) (waitingAt (releaseAt Release.p2))
idle-release-delivery : GP.step (GP.deliverCancellation (errorId 9)) (waitingAt (releaseAt Release.t4)) ≡ just idleCancelled
idle-release-delivery = refl
prune-release-delivery : GP.step (GP.deliverCancellation (errorId 9)) (waitingAt (releaseAt Release.p2)) ≡ just pruneCancelled
prune-release-delivery = refl
idle-write-preserved : CM.core (GP.cm idleCancelled) ≡ CM.core Release.t4
idle-write-preserved = refl
prune-writes-preserved : CM.core (GP.cm pruneCancelled) ≡ CM.core Release.p2
prune-writes-preserved = refl
prune-generator-write-preserved : CM.randomGeneration (GP.cm pruneCancelled) ≡ 2
prune-generator-write-preserved = refl
release-frame-detached : CM.releasing (GP.cm idleCancelled) ≡ []
release-frame-detached = refl
release-does-not-return : CM.released (GP.cm idleCancelled) ≡ CM.released Release.t4
release-does-not-return = refl
prune-captured-unsent-target : lookup j₀ (GP.unwinding pruneCancelled) ≡ just
  (Cancel.cancellation Release.caller (errorId 9)
    (Cancel.releasing (R.frame key₀ (R.prune (Release.victim ∷ []) Release.pruneResult) false))
    (Cancel.finished Cancel.abandoned))
prune-captured-unsent-target = refl
cancelled-release-cannot-resume : GP.step (GP.run (Sub.core (CM.release Release.caller R.selectWakeup))) idleCancelled ≡ nothing
cancelled-release-cannot-resume = refl

-- Closing the governor scope does not stop the independent IG worker.
import ConnectionManagement.Rules.IGRegistration as IG
igBefore : Inbound.Configuration
igBefore = CM.core (GP.cm bracketCancelled)
igAfter : Inbound.Configuration
igAfter = record igBefore { inboundGovernor = record (Inbound.inboundGovernor igBefore)
  { continuation = IG.armInactivity 0
  ; execution = record (IG.execution (Inbound.inboundGovernor igBefore)) { lastTime = 0 } } }
ig-progress-during-unwind : GP.step (GP.run (Sub.core (CM.inbound (Inbound.igStep (IG.captureTime 0))))) bracketCancelled ≡ just
  (GP.setCM (record (GP.cm bracketCancelled) { core = igAfter }) bracketCancelled)
ig-progress-during-unwind = refl
preResourceCancelled : GP.State
preResourceCancelled = after (GP.deliverCancellation (errorId 9)) (waitingAt g11)
pre-resource-delivery : GP.step (GP.deliverCancellation (errorId 9)) (waitingAt g11) ≡ just preResourceCancelled
pre-resource-delivery = refl
pre-resource-reservation-leaks : Inbound.world (CM.core (GP.cm preResourceCancelled)) ≡ O.reserved
pre-resource-reservation-leaks = refl
preHandoffClosed : GP.State
preHandoffClosed = after (GP.cleanup j₀ Cancel.closeSocket) preHandoffCancel
pre-handoff-real-close : GP.step (GP.cleanup j₀ Cancel.closeSocket) preHandoffCancel ≡ just preHandoffClosed
pre-handoff-real-close = refl
pre-handoff-closes-forked-socket : lookup O.sock (S.sockets (Inbound.world (CM.core (GP.cm preHandoffClosed)))) ≡ just S.closed
pre-handoff-closes-forked-socket = refl
post-handoff-has-no-caller-cleanup : GP.step (GP.cleanup j₀ Cancel.closeSocket) postHandoffCancel ≡ nothing
post-handoff-has-no-caller-cleanup = refl

-- Unlike the pre-resource cancellation run above, this initialized run opens
-- the real socket before cancellation, executes the actual bracket writers,
-- and joins the resulting Async handle. No injected caller snapshot is used.
openedPrefix : List GP.Action
openedPrefix = prefix ++ (GP.run L.a14 ∷ [])
opened-prefix-path : GP.Executes g₀ openedPrefix g14
opened-prefix-path = append prefix-path (GP.next initialized-step14 GP.done)
opened-close : GP.step (GP.beginClose (j₀ ∷ [])) g14 ≡ just (closingAt g14)
opened-close = refl
opened-select-current-handle : GP.step GP.requestCancel (closingAt g14) ≡ just (waitingAt g14)
opened-select-current-handle = refl
unwindBracket deregBracket asyncBracket joinedBracket closedBracket : GP.State
unwindBracket = record bracketDone { pool = record (GP.pool bracketDone)
  { handles = (j₀ , Pool.deregisterPending Pool.cancelledExit) ∷ [] } }
deregBracket = after (GP.deregisterCancelled j₀) unwindBracket
asyncBracket = after (GP.publishAsyncResult j₀) deregBracket
joinedBracket = after GP.join asyncBracket
closedBracket = after GP.finishClose joinedBracket
bracket-body-unwinds : GP.step (GP.bodyUnwound j₀) bracketDone ≡ just unwindBracket
bracket-body-unwinds = refl
bracket-cancelled-deregisters : GP.step (GP.deregisterCancelled j₀) unwindBracket ≡ just deregBracket
bracket-cancelled-deregisters = refl
bracket-async-result : GP.step (GP.publishAsyncResult j₀) deregBracket ≡ just asyncBracket
bracket-async-result = refl
bracket-handle-joins : GP.step GP.join asyncBracket ≡ just joinedBracket
bracket-handle-joins = refl
bracket-close-after-join : GP.step GP.finishClose joinedBracket ≡ just closedBracket
bracket-close-after-join = refl
bracketCloseActions : List GP.Action
bracketCloseActions = GP.beginClose (j₀ ∷ []) ∷ GP.requestCancel ∷
  GP.deliverCancellation (errorId 9) ∷ GP.cleanup j₀ Cancel.closeSocket ∷
  GP.cleanup j₀ Cancel.removeReservation ∷ GP.cleanup j₀ Cancel.readCounters ∷
  GP.bodyUnwound j₀ ∷ GP.deregisterCancelled j₀ ∷ GP.publishAsyncResult j₀ ∷
  GP.join ∷ GP.finishClose ∷ []
bracket-close-path : GP.Executes g14 bracketCloseActions closedBracket
bracket-close-path = GP.next opened-close (GP.next opened-select-current-handle
  (GP.next bracket-delivery (GP.next bracket-close (GP.next bracket-remove
  (GP.next bracket-count (GP.next bracket-body-unwinds
  (GP.next bracket-cancelled-deregisters (GP.next bracket-async-result
  (GP.next bracket-handle-joins (GP.next bracket-close-after-join GP.done))))))))))
initialized-bracket-close : GP.Executes g₀ (openedPrefix ++ bracketCloseActions) closedBracket
initialized-bracket-close = append opened-prefix-path bracket-close-path

-- The final state of that real initialized execution contains the committed
-- close/removal writes and no fabricated governor completion for cancellation.
initialized-bracket-socket-closed : lookup O.sock (S.sockets (Inbound.world (CM.core (GP.cm closedBracket)))) ≡ just S.closed
initialized-bracket-socket-closed = refl
initialized-bracket-map-removed : S.mapCell (S.cm (Inbound.world (CM.core (GP.cm closedBracket)))) ≡ S.full []
initialized-bracket-map-removed = refl
initialized-bracket-entry-terminated : lookup (ident 0) (S.entries (S.cm (Inbound.world (CM.core (GP.cm closedBracket))))) ≡ just (S.terminated nothing)
initialized-bracket-entry-terminated = refl
initialized-bracket-no-caller-return : CM.acquired (GP.cm closedBracket) ≡ []
initialized-bracket-no-caller-return = refl
initialized-bracket-no-failed-completion : Sub.completions (GP.machine closedBracket) ≡ []
initialized-bracket-no-failed-completion = refl
initialized-bracket-closed-phase : Pool.phase (GP.pool closedBracket) ≡ Pool.closedPool
initialized-bracket-closed-phase = refl
initialized-bracket-terminal : ∀ j → j ∈ Pool.snapshot (GP.pool closedBracket) → Cert.Close.Terminal (GP.pool closedBracket) j
initialized-bracket-terminal = Cert.from-initial initialized-bracket-close initialized-bracket-closed-phase

-- Supply induction retains the detached cleanup reference after removing the
-- original acquisition slot, and covers its actual writes through close.
import ConnectionManagement.Properties.GovernorPoolSupply as SupplyProof
open import Data.List.Relation.Unary.All using ([])
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
module Bounds = SupplyProof classify
initial-bounds : SupplyBounds (Inbound.world F.start)
initial-bounds = [] , []
initialized-cleaning-prefix : GP.Executes g₀
  (openedPrefix ++ (GP.beginClose (j₀ ∷ []) ∷ GP.requestCancel ∷
    GP.deliverCancellation (errorId 9) ∷ [])) bracketCancelled
initialized-cleaning-prefix = append opened-prefix-path
  (GP.next opened-close (GP.next opened-select-current-handle (GP.next bracket-delivery GP.done)))
detached-cleanup-capture-valid : Bounds.Valid bracketCancelled
detached-cleanup-capture-valid = Bounds.from-initial-valid initial-bounds initialized-cleaning-prefix
initialized-reservation-close-bounded : Bounds.Bounded closedOpen
initialized-reservation-close-bounded = Bounds.from-initial initial-bounds initialized-close
initialized-bracket-close-bounded : Bounds.Bounded closedBracket
initialized-bracket-close-bounded = Bounds.from-initial initial-bounds initialized-bracket-close

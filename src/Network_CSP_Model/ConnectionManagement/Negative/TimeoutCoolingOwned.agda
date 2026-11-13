{-# OPTIONS --guardedness #-}

-- Source timeout cleanup: handler finally directly terminates/purges outbound.
-- No CM release or TIME_WAIT is introduced. Each edge is the actual frontend.
module ConnectionManagement.Negative.TimeoutCoolingOwned where

open import ConnectionManagement.Negative.OutboundCleanLifecycleSupport
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.Rules.OutboundRelease as OutRelease
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.HandshakeContinuation as HS
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.IGTypes as Types
import Data.Maybe as Maybe
import ConnectionManagement.Negative.TimeoutCoolingMux as Prefix

import ConnectionManagement.Rules.MuxJobTypes as JobTypes
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.MuxRuntime as MuxRuntime

s0 : V.Runtime
s0 = Prefix.s24

a1 : V.Event
a1 = exit (W.beginExit L.child)
s1 : V.Runtime
s1 = snapshot (after a1 s0)
e1 : V.advance a1 s0 ≡ just s1
e1 = refl

a2 : V.Event
a2 = exit (W.observeBufferReturn L.child)
s2 : V.Runtime
s2 = snapshot (after a2 s1)
e2 : V.advance a2 s1 ≡ just s2
e2 = refl

a3 : V.Event
a3 = exit (W.enterFinalizer L.child)
s3 : V.Runtime
s3 = snapshot (after a3 s2)
e3 : V.advance a3 s2 ≡ just s3
e3 = refl

a4 : V.Event
a4 = exit (W.cleanup L.child Cleanup.takeCleanupMap)
s4 : V.Runtime
s4 = snapshot (after a4 s3)
e4 : V.advance a4 s3 ≡ just s4
e4 = refl

a5 : V.Event
a5 = exit (W.cleanup L.child Cleanup.selectCleanupEntry)
s5 : V.Runtime
s5 = snapshot (after a5 s4)
e5 : V.advance a5 s4 ≡ just s5
e5 = refl

a6 : V.Event
a6 = exit (W.cleanup L.child Cleanup.closeHandlerSocket)
s6 : V.Runtime
s6 = snapshot (after a6 s5)
e6 : V.advance a6 s5 ≡ just s6
e6 = refl

a7 : V.Event
a7 = exit (W.cleanup L.child Cleanup.publishCleanupMap)
s7 : V.Runtime
s7 = snapshot (after a7 s6)
e7 : V.advance a7 s6 ≡ just s7
e7 = refl

a8 : V.Event
a8 = exit (W.cleanup L.child Cleanup.readCleanupCounters)
s8 : V.Runtime
s8 = snapshot (after a8 s7)
e8 : V.advance a8 s7 ≡ just s8
e8 = refl

a9 : V.Event
a9 = exit (W.finishCleanup L.child)
s9 : V.Runtime
s9 = snapshot (after a9 s8)
e9 : V.advance a9 s8 ≡ just s9
e9 = refl

a10 : V.Event
a10 = exit (W.publishAsyncResult L.child)
s10 : V.Runtime
s10 = snapshot (after a10 s9)
e10 : V.advance a10 s9 ≡ just s10
e10 = refl

a11 : V.Event
a11 = V.pollResults (ident 0) (ident 50)
s11 : V.Runtime
s11 = snapshot (after a11 s10)
e11 : V.advance a11 s10 ≡ just s11
e11 = refl

a12 : V.Event
a12 = ps (Sub.jobStep (ident 1) J.observeCold)
s12 : V.Runtime
s12 = snapshot (after a12 s11)
e12 : V.advance a12 s11 ≡ just s12
e12 = refl

a13 : V.Event
a13 = ps (Sub.enqueueCompletion (ident 1) 0)
s13 : V.Runtime
s13 = snapshot (after a13 s12)
e13 : V.advance a13 s12 ≡ just s13
e13 = refl

a14 : V.Event
a14 = ps (Sub.deregisterJob (ident 1))
s14 : V.Runtime
s14 = snapshot (after a14 s13)
e14 : V.advance a14 s13 ≡ just s14
e14 = refl

a15 : V.Event
a15 = peer (PS.run (GP.publishAsyncResult (ident 1)))
s15 : V.Runtime
s15 = snapshot (after a15 s14)
e15 : V.advance a15 s14 ≡ just s15
e15 = refl

a16 : V.Event
a16 = peer (PS.finishMonitor (ident 50))
s16 : V.Runtime
s16 = snapshot (after a16 s15)
e16 : V.advance a16 s15 ≡ just s16
e16 = refl

a17 : V.Event
a17 = peer (PS.deregisterMonitor (ident 50))
s17 : V.Runtime
s17 = snapshot (after a17 s16)
e17 : V.advance a17 s16 ≡ just s17
e17 = refl

a18 : V.Event
a18 = peer (PS.publishMonitorResult (ident 50))
s18 : V.Runtime
s18 = snapshot (after a18 s17)
e18 : V.advance a18 s17 ≡ just s18
e18 = refl

actions : List V.Event
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ []

abstract
  path : V.Runs s0 actions s18
  path = V.more e1 (V.more e2 (V.more e3 (V.more e4 (V.more e5 (V.more e6 (V.more e7 (V.more e8 (V.more e9 (V.more e10 (V.more e11 (V.more e12 (V.more e13 (V.more e14 (V.more e15 (V.more e16 (V.more e17 (V.more e18 (V.stop))))))))))))))))))

import ConnectionManagement.Negative.OutboundCleanLifecycleAcquire as Acquisition
import ConnectionManagement.Negative.OutboundCleanLifecycleStartup as Startup
import ConnectionManagement.Negative.TimeoutCoolingEstablished as Established
import ConnectionManagement.Negative.TimeoutCoolingResults as Results
import ConnectionManagement.Negative.TimeoutCoolingOperation as Operation

-- Every segment begins at its predecessor's actual final successor.
schedule : List V.Event
schedule = Acquisition.actions ++ (Startup.actions ++ (Established.actions ++
  (Operation.actions ++ (Results.actions ++ (Prefix.actions ++ actions)))))
abstract
  initialized-to-completion : V.Runs initial schedule s18
  initialized-to-completion = append Acquisition.path (append Startup.path
    (append Established.path (append Operation.path (append Results.path (append Prefix.path path)))))
step-count : length schedule ≡ 145
step-count = refl

-- Small projections keep the endpoint and refusal claims inexpensive.
peerStatus : V.Runtime → Maybe.Maybe Peer.Status
peerStatus s = Maybe.map Peer.status (lookup (ident 0)
  (J.peers (Sub.world (PS.machine (K.peers (V.base s))))))
jobPC : V.Runtime → Maybe.Maybe J.PC
jobPC s = Maybe.map (λ jf → J.pc (Sub.execution jf))
  (lookup (ident 1) (Sub.jobs (PS.machine (K.peers (V.base s)))))

established-warm : peerStatus Established.s19 ≡ just Peer.peerWarm
established-warm = refl
operation-cooling : peerStatus Operation.s29 ≡ just Peer.peerCooling
operation-cooling = refl
operation-waits-for-cold : jobPC Operation.s29 ≡ just (J.awaitCold Governor.succeeded)
operation-waits-for-cold = refl
operation-did-not-release : lookup (ident 16) (O.releasing (source Operation.s29)) ≡ nothing
operation-did-not-release = refl
operation-queued-shutdown : Maybe.map MuxRuntime.commands
  (lookup (ident 0) (IG.muxes (IG.execution (governor Operation.s29)))) ≡ just (MuxRuntime.shutdown ∷ [])
operation-queued-shutdown = refl

socket-closed : lookup (ident 10) (Shared.sockets (shared s18)) ≡ just Shared.closed
socket-closed = refl
entry-terminated : lookup (ident 0) (Shared.entries (Shared.cm (shared s18))) ≡ just (Shared.terminated nothing)
entry-terminated = refl
connection-removed : Shared.mapCell (Shared.cm (shared s18)) ≡ Shared.full []
connection-removed = refl
cleanup-completed : lookup L.child (Shared.cleanups (shared s18)) ≡ just (Shared.cleanupDone Shared.cleanupNormal)
cleanup-completed = refl
handler-result : W.resultOf L.child (handlerState s18) ≡ just W.returned
handler-result = refl
peer-cold : peerStatus s18 ≡ just Peer.peerCold
peer-cold = refl
job-returned : jobPC s18 ≡ just (J.complete Governor.succeeded)
job-returned = refl
job-result : lookup (ident 1) (GP.Pool.handles (GP.pool (PS.governor (K.peers (V.base s18))))) ≡
  just (GP.Pool.resultAvailable GP.Pool.normalExit)
job-result = refl
monitor-result : lookup (ident 50) (PS.Pool.handles (PS.monitorPool (K.peers (V.base s18)))) ≡
  just (PS.Pool.resultAvailable PS.Pool.normalExit)
monitor-result = refl

-- Cleanup is direct, with no release frame or TIME_WAIT readiness.
no-release-frame : O.releasing (source s18) ≡ []
no-release-frame = refl
direct-cleanup : lookup L.child (Shared.cleanups (shared s7)) ≡
  just (Shared.cleanupCount Shared.cleanupNormal)
direct-cleanup = refl
cleanup-awaits-observation : peerStatus s7 ≡ just Peer.peerCooling
cleanup-awaits-observation = refl
no-timewait : V.advance (exit (W.cleanup L.child Cleanup.timeWaitElapsed)) s7 ≡ nothing
no-timewait = refl
no-timewait-finally : V.advance (exit (W.cleanup L.child Cleanup.finishTimeWait)) s7 ≡ nothing
no-timewait-finally = refl

-- Premature observations/results remain guarded on actual reached states.
no-all-results-before-protocol-return : V.advance (V.waitJobResults (ident 1)) Operation.s28 ≡ nothing
no-all-results-before-protocol-return = refl
no-cold-before-demotion : V.advance (V.pollResults (ident 0) (ident 50)) s0 ≡ nothing
no-cold-before-demotion = refl
no-cold-before-map-publication : V.advance (V.pollResults (ident 0) (ident 50)) s6 ≡ nothing
no-cold-before-map-publication = refl
no-cold-job-before-monitor : V.advance (ps (Sub.jobStep (ident 1) J.observeCold)) s10 ≡ nothing
no-cold-job-before-monitor = refl
no-job-return-before-cold : V.advance (ps (Sub.enqueueCompletion (ident 1) 0)) s10 ≡ nothing
no-job-return-before-cold = refl
no-physical-job-before-publication : V.advance (peer (PS.run (GP.publishAsyncResult (ident 1)))) s12 ≡ nothing
no-physical-job-before-publication = refl
no-handler-result-before-cleanup : V.advance (exit (W.publishAsyncResult L.child)) s7 ≡ nothing
no-handler-result-before-cleanup = refl
no-monitor-result-before-body : V.advance (peer (PS.publishMonitorResult (ident 50))) s15 ≡ nothing
no-monitor-result-before-body = refl
no-demotion-timeout-at-operation-wait : V.advance (ps (Sub.jobStep (ident 1) J.demotionTimeout)) Operation.s28 ≡ nothing
no-demotion-timeout-at-operation-wait = refl

-- Separate diagnostic outcome; never inserted into the main history.
demotion-expired : V.Runtime
demotion-expired = snapshot (after (ps (Sub.jobStep (ident 1) J.demotionTimeout)) s0)
demotion-edge : V.advance (ps (Sub.jobStep (ident 1) J.demotionTimeout)) s0 ≡ just demotion-expired
demotion-edge = refl
demotion-distinct-outcome : jobPC demotion-expired ≡ just (J.complete Governor.demotionTimedOut)
demotion-distinct-outcome = refl
demotion-retains-cooling : peerStatus demotion-expired ≡ just Peer.peerCooling
demotion-retains-cooling = refl
-- Timeout is observed while a real configured warm initiator still runs.
operation-has-pending-result : Maybe.map (λ p → Peer.all Types.warm (Peer.runs p))
  (lookup (ident 0) (J.peers (Sub.world (PS.machine (K.peers (V.base Operation.s28)))))) ≡ just nothing
operation-has-pending-result = refl
operation-is-not-timewait : lookup L.child (Shared.cleanups (shared Operation.s29)) ≡ nothing
operation-is-not-timewait = refl
monitor-observes-cold : peerStatus s11 ≡ just Peer.peerCold
monitor-observes-cold = refl

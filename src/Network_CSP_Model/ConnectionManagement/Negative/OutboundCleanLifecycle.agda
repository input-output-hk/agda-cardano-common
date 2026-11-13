{-# OPTIONS --guardedness #-}

-- Literal snapshots normalize one actual successor; independent refl edges
-- reject every refused step. No midpoint is supplied as an initial state.
module ConnectionManagement.Negative.OutboundCleanLifecycle where

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
import ConnectionManagement.Negative.OutboundCleanLifecycleRelease as Prefix

s0 : V.Runtime
s0 = Prefix.s38

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
a8 = exit (W.deliverReleaseTimeWait (ident 16) (errorId 42))
s8 : V.Runtime
s8 = snapshot (after a8 s7)
e8 : V.advance a8 s7 ≡ just s8
e8 = refl

a9 : V.Event
a9 = outRelease OutRelease.returnResult
s9 : V.Runtime
s9 = snapshot (after a9 s8)
e9 : V.advance a9 s8 ≡ just s9
e9 = refl

a10 : V.Event
a10 = ps (Sub.jobStep (ident 1) J.collectRelease)
s10 : V.Runtime
s10 = snapshot (after a10 s9)
e10 : V.advance a10 s9 ≡ just s10
e10 = refl

a11 : V.Event
a11 = exit (W.cleanup L.child Cleanup.finishTimeWait)
s11 : V.Runtime
s11 = snapshot (after a11 s10)
e11 : V.advance a11 s10 ≡ just s11
e11 = refl

a12 : V.Event
a12 = exit (W.cleanup L.child Cleanup.readCleanupCounters)
s12 : V.Runtime
s12 = snapshot (after a12 s11)
e12 : V.advance a12 s11 ≡ just s12
e12 = refl

a13 : V.Event
a13 = exit (W.finishCleanup L.child)
s13 : V.Runtime
s13 = snapshot (after a13 s12)
e13 : V.advance a13 s12 ≡ just s13
e13 = refl

a14 : V.Event
a14 = exit (W.publishAsyncResult L.child)
s14 : V.Runtime
s14 = snapshot (after a14 s13)
e14 : V.advance a14 s13 ≡ just s14
e14 = refl

a15 : V.Event
a15 = V.pollResults (ident 0) (ident 50)
s15 : V.Runtime
s15 = snapshot (after a15 s14)
e15 : V.advance a15 s14 ≡ just s15
e15 = refl

a16 : V.Event
a16 = ps (Sub.jobStep (ident 1) J.observeCold)
s16 : V.Runtime
s16 = snapshot (after a16 s15)
e16 : V.advance a16 s15 ≡ just s16
e16 = refl

a17 : V.Event
a17 = ps (Sub.enqueueCompletion (ident 1) 0)
s17 : V.Runtime
s17 = snapshot (after a17 s16)
e17 : V.advance a17 s16 ≡ just s17
e17 = refl

a18 : V.Event
a18 = ps (Sub.deregisterJob (ident 1))
s18 : V.Runtime
s18 = snapshot (after a18 s17)
e18 : V.advance a18 s17 ≡ just s18
e18 = refl

a19 : V.Event
a19 = peer (PS.run (GP.publishAsyncResult (ident 1)))
s19 : V.Runtime
s19 = snapshot (after a19 s18)
e19 : V.advance a19 s18 ≡ just s19
e19 = refl

actions : List V.Event
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ a19 ∷ []

abstract
  path : V.Runs s0 actions s19
  path = V.more e1 (V.more e2 (V.more e3 (V.more e4 (V.more e5 (V.more e6 (V.more e7 (V.more e8 (V.more e9 (V.more e10 (V.more e11 (V.more e12 (V.more e13 (V.more e14 (V.more e15 (V.more e16 (V.more e17 (V.more e18 (V.more e19 (V.stop)))))))))))))))))))

import ConnectionManagement.Negative.OutboundCleanLifecycleAcquire as Acquisition
import ConnectionManagement.Negative.OutboundCleanLifecycleStartup as Startup
import ConnectionManagement.Negative.OutboundCleanLifecycleProtocol as Protocol
import ConnectionManagement.Negative.OutboundCleanLifecycleMux as Mux
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.MuxJobTypes as Jobs
import ConnectionManagement.Rules.MuxRuntime as MuxRuntime

-- The sole configured protocol is warm/on-demand, initiator direction. Hot
-- and established bundles are empty. There is no retained inbound bearer role.
schedule : List V.Event
schedule = Acquisition.actions ++ (Startup.actions ++ (Protocol.actions ++ (Mux.actions ++ (Prefix.actions ++ actions))))
abstract
  initialized-to-completion : V.Runs initial schedule s19
  initialized-to-completion = append Acquisition.path (append Startup.path
    (append Protocol.path (append Mux.path (append Prefix.path path))))
step-count : length schedule ≡ 156
step-count = refl
protocol-clean : Maybe.map Jobs.phase (lookup (ident 10) (P.jobs (V.physical (V.base s19)))) ≡ just (Jobs.resultCaptured Types.clean)
protocol-clean = refl
mux-normal-exit : G.phase (G.frameAt L.child (V.group (V.base s19))) ≡ G.scopeDone G.normalExit
mux-normal-exit = refl
pool-closed : Pool.phase (G.poolAt L.child (V.group (V.base s19))) ≡ Pool.closedPool
pool-closed = refl
socket-closed : lookup (ident 10) (Shared.sockets (shared s19)) ≡ just Shared.closed
socket-closed = refl
entry-terminated : lookup (ident 0) (Shared.entries (Shared.cm (shared s19))) ≡ just (Shared.terminated nothing)
entry-terminated = refl
connection-removed : Shared.mapCell (Shared.cm (shared s19)) ≡ Shared.full []
connection-removed = refl
release-returned : lookup (ident 16) (O.released (source s19)) ≡
  just (OutRelease.success (just (Shared.terminating A.key₀ L.child nothing)))
release-returned = refl
release-frame-retired : lookup (ident 16) (O.releasing (source s19)) ≡ nothing
release-frame-retired = refl
cleanup-finished : lookup L.child (Shared.cleanups (shared s19)) ≡ just (Shared.cleanupDone (Shared.cleanupError (errorId 42)))
cleanup-finished = refl
physical-result : W.resultOf L.child (handlerState s19) ≡ just (W.asyncException (errorId 42))
physical-result = refl
peer-cold : Maybe.map Peer.status (lookup (ident 0) (J.peers (Sub.world (PS.machine (K.peers (V.base s19)))))) ≡ just Peer.peerCold
peer-cold = refl
close-job-returned : Maybe.map (λ jf → J.pc (Sub.execution jf))
  (lookup (ident 1) (Sub.jobs (PS.machine (K.peers (V.base s19))))) ≡ just (J.complete Governor.succeeded)
close-job-returned = refl
close-job-physical-result : Maybe.map (λ { (GP.Pool.resultAvailable _) → true ; _ → false })
  (lookup (ident 1) (GP.Pool.handles (GP.pool (PS.governor (K.peers (V.base s19)))))) ≡ just true
close-job-physical-result = refl
no-retained-inbound-owner : IG.connections (IG.publishedState (governor s19)) ≡ []
no-retained-inbound-owner = refl
-- Role release is NOT generally bearer teardown: the ticking duplex branch
-- retains inbound ownership and has no cancel/delivering continuation.
duplex-role-release-retains-inbound : OutRelease.branch A.key₀ (ident 0)
  (Shared.outboundDup A.key₀ L.child (ident 0) ticking) ≡
  OutRelease.decision (just (Shared.inboundIdle A.key₀ L.child (ident 0) duplex))
    (OutRelease.count (OutRelease.complete (OutRelease.success
      (just (Shared.outboundDup A.key₀ L.child (ident 0) ticking))))) true
duplex-role-release-retains-inbound = refl
no-release-return-before-receipt : V.advance (outRelease OutRelease.returnResult) s7 ≡ nothing
no-release-return-before-receipt = refl
no-raw-release-receipt : V.advance (outRelease (OutRelease.cancellationDelivered L.child)) s7 ≡ nothing
no-raw-release-receipt = refl
no-timewait-receipt-before-delay : V.advance (exit (W.deliverReleaseTimeWait (ident 16) (errorId 42))) s0 ≡ nothing
no-timewait-receipt-before-delay = refl
no-finished-receipt-before-result : V.advance (exit (W.acknowledgeReleaseFinished (ident 16))) s7 ≡ nothing
no-finished-receipt-before-result = refl
receipt-does-not-publish-result : W.resultOf L.child (handlerState s8) ≡ nothing
receipt-does-not-publish-result = refl
no-duplicate-receipt : V.advance (exit (W.deliverReleaseTimeWait (ident 16) (errorId 42))) s8 ≡ nothing
no-duplicate-receipt = refl
no-result-before-timewait-finally : V.advance (exit (W.publishAsyncResult L.child)) s8 ≡ nothing
no-result-before-timewait-finally = refl
no-cleanup-before-body-exit : V.advance (exit (W.cleanup L.child Cleanup.takeCleanupMap)) s0 ≡ nothing
no-cleanup-before-body-exit = refl
no-exit-before-mux-scope : V.advance (exit (W.beginExit L.child)) Protocol.s31 ≡ nothing
no-exit-before-mux-scope = refl
no-collect-before-return : V.advance (ps (Sub.jobStep (ident 1) J.collectRelease)) s8 ≡ nothing
no-collect-before-return = refl
no-cold-job-before-monitor : V.advance (ps (Sub.jobStep (ident 1) J.observeCold)) s14 ≡ nothing
no-cold-job-before-monitor = refl

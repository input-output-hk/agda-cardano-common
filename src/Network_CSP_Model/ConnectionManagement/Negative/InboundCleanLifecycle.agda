{-# OPTIONS --guardedness #-}

-- G2 initialized inbound clean lifecycle; the original 94-event diagnostic
-- prefix and its theorem statements are retained below. Physical receipt now
-- continues through TIME_WAIT cleanup, IG commit and handler Async result.
-- Admission, IG registration, a real responder clean result and graceful mux
-- normal exit are reached from the supervised initializer. The original
-- diagnostic prefix ends at pending release: the raw route remains sealed and
-- outbound adapters still require OUTBOUND release frames.
-- The old raw/outbound routes remain refused; the new inbound suffix follows.
-- Negotiation, one traffic demand, tracer/DeltaQ returns, empty egress drain,
-- infrastructure unwind and idle expiry are supplied boundary observations.
module ConnectionManagement.Negative.InboundCleanLifecycle where

open import ConnectionManagement.Negative.InboundCleanLifecycleSupport
import Data.Maybe
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.InboundCleanLifecycleMux as Mux
import ConnectionManagement.Negative.InboundCleanLifecycleAdmission as AdmissionPrefix
import ConnectionManagement.Negative.InboundCleanLifecycleProtocol as Protocol
import ConnectionManagement.HandlerSupervision as Physical
import ConnectionManagement.Rules.MuxRuntime as MuxRuntime
import ConnectionManagement.Rules.MuxJobTypes as Types
s0 : V.Runtime
s0 = Mux.s27

a1 : V.Event
a1 = ig (IG.expireTimer (ident 1))
s1 : V.Runtime
s1 = snapshot (after a1 s0)
e1 : V.advance a1 s0 ≡ just s1
e1 = refl

a2 : V.Event
a2 = ig (IG.captureTime 11)
s2 : V.Runtime
s2 = snapshot (after a2 s1)
e2 : V.advance a2 s1 ≡ just s2
e2 = refl

a3 : V.Event
a3 = ig IG.registerInactivity
s3 : V.Runtime
s3 = snapshot (after a3 s2)
e3 : V.advance a3 s2 ≡ just s3
e3 = refl

a4 : V.Event
a4 = ig IG.selectBatch
s4 : V.Runtime
s4 = snapshot (after a4 s3)
e4 : V.advance a4 s3 ≡ just s4
e4 = refl

a5 : V.Event
a5 = ig IG.readEvent
s5 : V.Runtime
s5 = snapshot (after a5 s4)
e5 : V.advance a5 s4 ≡ just s5
e5 = refl

a6 : V.Event
a6 = release Release.enter
s6 : V.Runtime
s6 = snapshot (after a6 s5)
e6 : V.advance a6 s5 ≡ just s6
e6 = refl

a7 : V.Event
a7 = release Release.transact
s7 : V.Runtime
s7 = snapshot (after a7 s6)
e7 : V.advance a7 s6 ≡ just s7
e7 = refl

a8 : V.Event
a8 = release Release.readCounters
s8 : V.Runtime
s8 = snapshot (after a8 s7)
e8 : V.advance a8 s7 ≡ just s8
e8 = refl

a9 : V.Event
a9 = release Release.requestCancellation
s9 : V.Runtime
s9 = snapshot (after a9 s8)
e9 : V.advance a9 s8 ≡ just s9
e9 = refl

actions : List V.Event
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ []

abstract
  path : V.Runs s0 actions s9
  path = V.more e1 (V.more e2 (V.more e3 (V.more e4 (V.more e5 (V.more e6 (V.more e7 (V.more e8 (V.more e9 (V.stop)))))))))

-- Small compositional run concatenation; no whole-history normalization.
append : ∀ {s as t bs u} → V.Runs s as t → V.Runs t bs u → V.Runs s (as ++ bs) u
append V.stop tail = tail
append (V.more edge rest) tail = V.more edge (append rest tail)

schedule : List V.Event
schedule = AdmissionPrefix.actions ++ (Protocol.actions ++ (Mux.actions ++ actions))
abstract
  initialized-to-obstruction : V.Runs initial schedule s9
  initialized-to-obstruction = append AdmissionPrefix.path
    (append Protocol.path (append Mux.path path))

step-count : length schedule ≡ 94
step-count = refl

-- Exact physical outer state at the obstruction, not a substitute midpoint.
handlerState : V.Runtime → W.State
handlerState s = N.R.base (N.raw (V.publication (V.base s)))

mux-normal-exit : G.phase (G.frameAt A.child₀ (V.group (V.base s9))) ≡ G.scopeDone G.normalExit
mux-normal-exit = refl
pool-closed : Pool.phase (G.poolAt A.child₀ (V.group (V.base s9))) ≡ Pool.closedPool
pool-closed = refl
mux-stopped : Data.Maybe.map MuxRuntime.status
  (lookup (ident 0) (IG.muxes (IG.execution (governor s9)))) ≡ just MuxRuntime.stopped
mux-stopped = refl
protocol-clean : Data.Maybe.map Types.phase
  (lookup (ident 10) (P.jobs (V.physical (V.base s9)))) ≡ just (Types.resultCaptured IG.clean)
protocol-clean = refl
release-waits-for-actual-handler :
  Data.Maybe.map Release.pc (Machine.inboundRelease (O.core (source s9))) ≡ just (Release.delivering A.child₀)
release-waits-for-actual-handler = refl
entry-terminating : lookup (ident 0) (Shared.entries (Shared.cm (shared s9))) ≡
  just (Shared.terminating A.key₀ A.child₀ nothing)
entry-terminating = refl
socket-still-owned : lookup (ident 0) (Shared.sockets (shared s9)) ≡ just (Shared.handling A.child₀)
socket-still-owned = refl
no-cleanup-started : lookup A.child₀ (Shared.cleanups (shared s9)) ≡ nothing
no-cleanup-started = refl
handler-result-unavailable : W.resultOf A.child₀ (handlerState s9) ≡ nothing
handler-result-unavailable = refl
ig-still-tracking : IG.publishedState (governor s9) ≡ IG.publishedState (governor AdmissionPrefix.s38)
ig-still-tracking = refl

-- Historical obstruction controls: the source transaction runs, while the raw
-- and outbound routes still refuse. The new inbound receipt is tested below.
raw-inbound-receipt-sealed : ∀ w → Physical.rawAllowed (Machine.releaseStep (Release.cancellationDelivered w)) ≡ false
raw-inbound-receipt-sealed w = refl
actual-inbound-receipt-refused : V.advance (release (Release.cancellationDelivered A.child₀)) s9 ≡ nothing
actual-inbound-receipt-refused = refl
outbound-frame-absent : lookup A.w₀ (O.releasing (source s9)) ≡ nothing
outbound-frame-absent = refl
outbound-mux-adapter-refused : V.advance (exit (W.deliverReleaseMux A.w₀ (errorId 42))) s9 ≡ nothing
outbound-mux-adapter-refused = refl
outbound-finished-adapter-refused : V.advance (exit (W.acknowledgeReleaseFinished A.w₀)) s9 ≡ nothing
outbound-finished-adapter-refused = refl
outbound-timewait-adapter-refused : V.advance (exit (W.deliverReleaseTimeWait A.w₀ (errorId 42))) s9 ≡ nothing
outbound-timewait-adapter-refused = refl
no-return-before-receipt : V.advance (release Release.returnToIG) s9 ≡ nothing
no-return-before-receipt = refl
no-assertion-before-receipt : V.advance (release Release.checkAssertion) s9 ≡ nothing
no-assertion-before-receipt = refl
no-result-before-cleanup : V.advance (exit (W.publishAsyncResult A.child₀)) s9 ≡ nothing
no-result-before-cleanup = refl
no-cleanup-before-finalizer : V.advance (exit (W.cleanup A.child₀ Cleanup.takeCleanupMap)) s9 ≡ nothing
no-cleanup-before-finalizer = refl
no-release-before-commit-selection : V.advance (release Release.enter) AdmissionPrefix.s38 ≡ nothing
no-release-before-commit-selection = refl
no-handler-exit-before-mux-scope : V.advance (exit (W.beginExit A.child₀)) Protocol.s20 ≡ nothing
no-handler-exit-before-mux-scope = refl

-- Normal mux/body return reaches the unmasked TIME_WAIT in CM finally.

a10 : V.Event
a10 = exit (W.beginExit A.child₀)
s10 : V.Runtime
s10 = snapshot (after a10 s9)
e10 : V.advance a10 s9 ≡ just s10
e10 = refl

a11 : V.Event
a11 = exit (W.observeBufferReturn A.child₀)
s11 : V.Runtime
s11 = snapshot (after a11 s10)
e11 : V.advance a11 s10 ≡ just s11
e11 = refl

a12 : V.Event
a12 = exit (W.enterFinalizer A.child₀)
s12 : V.Runtime
s12 = snapshot (after a12 s11)
e12 : V.advance a12 s11 ≡ just s12
e12 = refl

a13 : V.Event
a13 = exit (W.cleanup A.child₀ Cleanup.takeCleanupMap)
s13 : V.Runtime
s13 = snapshot (after a13 s12)
e13 : V.advance a13 s12 ≡ just s13
e13 = refl

a14 : V.Event
a14 = exit (W.cleanup A.child₀ Cleanup.selectCleanupEntry)
s14 : V.Runtime
s14 = snapshot (after a14 s13)
e14 : V.advance a14 s13 ≡ just s14
e14 = refl

a15 : V.Event
a15 = exit (W.cleanup A.child₀ Cleanup.closeHandlerSocket)
s15 : V.Runtime
s15 = snapshot (after a15 s14)
e15 : V.advance a15 s14 ≡ just s15
e15 = refl

a16 : V.Event
a16 = exit (W.cleanup A.child₀ Cleanup.publishCleanupMap)
s16 : V.Runtime
s16 = snapshot (after a16 s15)
e16 : V.advance a16 s15 ≡ just s16
e16 = refl

a17 : V.Event
a17 = exit (W.deliverInboundReleaseTimeWait (errorId 42))
s17 : V.Runtime
s17 = snapshot (after a17 s16)
e17 : V.advance a17 s16 ≡ just s17
e17 = refl

a18 : V.Event
a18 = release Release.checkAssertion
s18 : V.Runtime
s18 = snapshot (after a18 s17)
e18 : V.advance a18 s17 ≡ just s18
e18 = refl

a19 : V.Event
a19 = release Release.returnToIG
s19 : V.Runtime
s19 = snapshot (after a19 s18)
e19 : V.advance a19 s18 ≡ just s19
e19 = refl

a20 : V.Event
a20 = ig IG.commitDecision
s20 : V.Runtime
s20 = snapshot (after a20 s19)
e20 : V.advance a20 s19 ≡ just s20
e20 = refl

a21 : V.Event
a21 = exit (W.cleanup A.child₀ Cleanup.finishTimeWait)
s21 : V.Runtime
s21 = snapshot (after a21 s20)
e21 : V.advance a21 s20 ≡ just s21
e21 = refl

a22 : V.Event
a22 = exit (W.cleanup A.child₀ Cleanup.readCleanupCounters)
s22 : V.Runtime
s22 = snapshot (after a22 s21)
e22 : V.advance a22 s21 ≡ just s22
e22 = refl

a23 : V.Event
a23 = exit (W.finishCleanup A.child₀)
s23 : V.Runtime
s23 = snapshot (after a23 s22)
e23 : V.advance a23 s22 ≡ just s23
e23 = refl

a24 : V.Event
a24 = exit (W.publishAsyncResult A.child₀)
s24 : V.Runtime
s24 = snapshot (after a24 s23)
e24 : V.advance a24 s23 ≡ just s24
e24 = refl

completionActions : List V.Event
completionActions = a10 ∷ a11 ∷ a12 ∷ a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ a19 ∷ a20 ∷ a21 ∷ a22 ∷ a23 ∷ a24 ∷ []

abstract
  completion : V.Runs s9 completionActions s24
  completion = V.more e10 (V.more e11 (V.more e12 (V.more e13 (V.more e14 (V.more e15 (V.more e16 (V.more e17 (V.more e18 (V.more e19 (V.more e20 (V.more e21 (V.more e22 (V.more e23 (V.more e24 (V.stop)))))))))))))))

  initialized-to-completion : V.Runs initial (schedule ++ completionActions) s24
  initialized-to-completion = append initialized-to-obstruction completion

complete-step-count : length (schedule ++ completionActions) ≡ 109
complete-step-count = refl
socket-closed : lookup (ident 0) (Shared.sockets (shared s24)) ≡ just Shared.closed
socket-closed = refl
entry-terminated : lookup (ident 0) (Shared.entries (Shared.cm (shared s24))) ≡ just (Shared.terminated nothing)
entry-terminated = refl
connection-removed : Shared.mapCell (Shared.cm (shared s24)) ≡ Shared.full []
connection-removed = refl
ig-unregistered : IG.connections (IG.publishedState (governor s24)) ≡ []
ig-unregistered = refl
inbound-call-returned : Machine.inboundRelease (O.core (source s24)) ≡ nothing
inbound-call-returned = refl
cleanup-finished : lookup A.child₀ (Shared.cleanups (shared s24)) ≡ just (Shared.cleanupDone (Shared.cleanupError (errorId 42)))
cleanup-finished = refl
physical-result : W.resultOf A.child₀ (handlerState s24) ≡ just (W.asyncException (errorId 42))
physical-result = refl
physical-result-ready : W.resultReady A.child₀ (handlerState s24) ≡ true
physical-result-ready = refl
receipt-without-pending-call : V.advance (exit (W.deliverInboundReleaseTimeWait (errorId 42))) s0 ≡ nothing
receipt-without-pending-call = refl
mux-receipt-without-pending-call : V.advance (exit (W.deliverInboundReleaseMux (errorId 42))) s0 ≡ nothing
mux-receipt-without-pending-call = refl
finished-receipt-without-pending-call : V.advance (exit W.acknowledgeInboundReleaseFinished) s0 ≡ nothing
finished-receipt-without-pending-call = refl
receipt-before-unmasked-delay : V.advance (exit (W.deliverInboundReleaseTimeWait (errorId 42))) s9 ≡ nothing
receipt-before-unmasked-delay = refl
duplicate-inbound-receipt : V.advance (exit (W.deliverInboundReleaseTimeWait (errorId 42))) s17 ≡ nothing
duplicate-inbound-receipt = refl
finished-receipt-needs-physical-result : V.advance (exit W.acknowledgeInboundReleaseFinished) s16 ≡ nothing
finished-receipt-needs-physical-result = refl
receipt-does-not-publish-result : W.resultOf A.child₀ (handlerState s17) ≡ nothing
receipt-does-not-publish-result = refl
no-result-before-timewait-finally : V.advance (exit (W.publishAsyncResult A.child₀)) s17 ≡ nothing
no-result-before-timewait-finally = refl
normal-mux-at-completion : G.phase (G.frameAt A.child₀ (V.group (V.base s24))) ≡ G.scopeDone G.normalExit
normal-mux-at-completion = refl
clean-responder-at-completion : Data.Maybe.map Types.phase
  (lookup (ident 10) (P.jobs (V.physical (V.base s24)))) ≡ just (Types.resultCaptured IG.clean)
clean-responder-at-completion = refl

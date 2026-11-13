{-# OPTIONS --guardedness #-}

-- G2 / DESIGN §9 diagnostic, not a completed clean lifecycle.
-- Admission, IG registration, a real responder clean result and graceful mux
-- normal exit are reached from the supervised initializer. The subsequent IG
-- inbound release stalls at its physical cancellation acknowledgement: the raw
-- route is sealed, while the physical adapters inspect OUTBOUND release frames.
-- Stop here without weakening guards or inventing cleanup/result success.
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

-- The source release transaction itself really runs; the physical receipt does
-- not. This is the named adapter obstruction, not a source-code defect claim.
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

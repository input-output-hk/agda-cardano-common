{-# OPTIONS --guardedness #-}

-- Literal snapshots normalize one actual successor; independent refl edges
-- reject every refused step. No midpoint is supplied as an initial state.
module ConnectionManagement.Negative.OutboundCleanLifecycleAcquire where

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
import ConnectionManagement.Scenarios.Admission as A

s0 : V.Runtime
s0 = initial

a1 : V.Event
a1 = ps L.a1
s1 : V.Runtime
s1 = snapshot (after a1 s0)
e1 : V.advance a1 s0 ≡ just s1
e1 = refl

a2 : V.Event
a2 = ps L.a2
s2 : V.Runtime
s2 = snapshot (after a2 s1)
e2 : V.advance a2 s1 ≡ just s2
e2 = refl

a3 : V.Event
a3 = ps L.a3
s3 : V.Runtime
s3 = snapshot (after a3 s2)
e3 : V.advance a3 s2 ≡ just s3
e3 = refl

a4 : V.Event
a4 = ps L.a4
s4 : V.Runtime
s4 = snapshot (after a4 s3)
e4 : V.advance a4 s3 ≡ just s4
e4 = refl

a5 : V.Event
a5 = ps L.a5
s5 : V.Runtime
s5 = snapshot (after a5 s4)
e5 : V.advance a5 s4 ≡ just s5
e5 = refl

a6 : V.Event
a6 = ps L.a6
s6 : V.Runtime
s6 = snapshot (after a6 s5)
e6 : V.advance a6 s5 ≡ just s6
e6 = refl

a7 : V.Event
a7 = ps L.a7
s7 : V.Runtime
s7 = snapshot (after a7 s6)
e7 : V.advance a7 s6 ≡ just s7
e7 = refl

a8 : V.Event
a8 = ps L.a8
s8 : V.Runtime
s8 = snapshot (after a8 s7)
e8 : V.advance a8 s7 ≡ just s8
e8 = refl

a9 : V.Event
a9 = ps L.a9
s9 : V.Runtime
s9 = snapshot (after a9 s8)
e9 : V.advance a9 s8 ≡ just s9
e9 = refl

a10 : V.Event
a10 = ps L.a10
s10 : V.Runtime
s10 = snapshot (after a10 s9)
e10 : V.advance a10 s9 ≡ just s10
e10 = refl

a11 : V.Event
a11 = acquire (Acquire.select nothing)
s11 : V.Runtime
s11 = snapshot (after a11 s10)
e11 : V.advance a11 s10 ≡ just s11
e11 = refl

a12 : V.Event
a12 = acquire Acquire.readCounters
s12 : V.Runtime
s12 = snapshot (after a12 s11)
e12 : V.advance a12 s11 ≡ just s12
e12 = refl

a13 : V.Event
a13 = acquire Acquire.newPromise
s13 : V.Runtime
s13 = snapshot (after a13 s12)
e13 : V.advance a13 s12 ≡ just s13
e13 = refl

a14 : V.Event
a14 = acquire Acquire.openOK
s14 : V.Runtime
s14 = snapshot (after a14 s13)
e14 : V.advance a14 s13 ≡ just s14
e14 = refl

a15 : V.Event
a15 = acquire Acquire.configureOK
s15 : V.Runtime
s15 = snapshot (after a15 s14)
e15 : V.advance a15 s14 ≡ just s15
e15 = refl

a16 : V.Event
a16 = acquire Acquire.connectOK
s16 : V.Runtime
s16 = snapshot (after a16 s15)
e16 : V.advance a16 s15 ≡ just s16
e16 = refl

a17 : V.Event
a17 = acquire (Acquire.gotLocal (ConnectionKey.local A.key₀))
s17 : V.Runtime
s17 = snapshot (after a17 s16)
e17 : V.advance a17 s16 ≡ just s17
e17 = refl

a18 : V.Event
a18 = acquire Acquire.updateLocalAddress
s18 : V.Runtime
s18 = snapshot (after a18 s17)
e18 : V.advance a18 s17 ≡ just s18
e18 = refl

a19 : V.Event
a19 = acquire Acquire.forkOK
s19 : V.Runtime
s19 = snapshot (after a19 s18)
e19 : V.advance a19 s18 ≡ just s19
e19 = refl

a20 : V.Event
a20 = peer (PS.run (GP.handoff L.caller))
s20 : V.Runtime
s20 = snapshot (after a20 s19)
e20 : V.advance a20 s19 ≡ just s20
e20 = refl

a21 : V.Event
a21 = acquire Acquire.commitConnected
s21 : V.Runtime
s21 = snapshot (after a21 s20)
e21 : V.advance a21 s20 ≡ just s21
e21 = refl

a22 : V.Event
a22 = acquire Acquire.readCounters
s22 : V.Runtime
s22 = snapshot (after a22 s21)
e22 : V.advance a22 s21 ≡ just s22
e22 = refl

a23 : V.Event
a23 = server (E.run (handler (H.enterHandshake L.child)))
s23 : V.Runtime
s23 = snapshot (after a23 s22)
e23 : V.advance a23 s22 ≡ just s23
e23 = refl

actions : List V.Event
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ a19 ∷ a20 ∷ a21 ∷ a22 ∷ a23 ∷ []

abstract
  path : V.Runs s0 actions s23
  path = V.more e1 (V.more e2 (V.more e3 (V.more e4 (V.more e5 (V.more e6 (V.more e7 (V.more e8 (V.more e9 (V.more e10 (V.more e11 (V.more e12 (V.more e13 (V.more e14 (V.more e15 (V.more e16 (V.more e17 (V.more e18 (V.more e19 (V.more e20 (V.more e21 (V.more e22 (V.more e23 (V.stop)))))))))))))))))))))))

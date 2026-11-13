{-# OPTIONS --guardedness #-}

-- Actual successor snapshots, with independent refl evidence for every edge.
module ConnectionManagement.Negative.OverlapInitialized13 where

open import ConnectionManagement.Negative.InboundCleanLifecycleSupport
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

import ConnectionManagement.Negative.InboundCleanLifecycle as Old
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Negative.OverlapInitialized12 as Prefix

s0 : V.Runtime
s0 = Prefix.final

a1 : V.Event
a1 = ig IG.readEvent
s1 : V.Runtime
s1 = snapshot (after a1 s0)
e1 : V.advance a1 s0 ≡ just s1
e1 = refl

a2 : V.Event
a2 = server (E.run (S.run (S.runMachine (Machine.remoteStep Remote.enter))))
s2 : V.Runtime
s2 = snapshot (after a2 s1)
e2 : V.advance a2 s1 ≡ just s2
e2 = refl

a3 : V.Event
a3 = server (E.run (S.run (S.runMachine (Machine.remoteStep Remote.transact))))
s3 : V.Runtime
s3 = snapshot (after a3 s2)
e3 : V.advance a3 s2 ≡ just s3
e3 = refl

a4 : V.Event
a4 = server (E.run (S.run (S.runMachine (Machine.remoteStep Remote.checkAssertion))))
s4 : V.Runtime
s4 = snapshot (after a4 s3)
e4 : V.advance a4 s3 ≡ just s4
e4 = refl

a5 : V.Event
a5 = server (E.run (S.run (S.runMachine (Machine.remoteStep Remote.readCounters))))
s5 : V.Runtime
s5 = snapshot (after a5 s4)
e5 : V.advance a5 s4 ≡ just s5
e5 = refl

a6 : V.Event
a6 = server (E.run (S.run (S.runMachine (Machine.remoteStep Remote.returnToIG))))
s6 : V.Runtime
s6 = snapshot (after a6 s5)
e6 : V.advance a6 s5 ≡ just s6
e6 = refl

a7 : V.Event
a7 = ig IG.readEvent
s7 : V.Runtime
s7 = snapshot (after a7 s6)
e7 : V.advance a7 s6 ≡ just s7
e7 = refl

a8 : V.Event
a8 = ig IG.finishBatch
s8 : V.Runtime
s8 = snapshot (after a8 s7)
e8 : V.advance a8 s7 ≡ just s8
e8 = refl

a9 : V.Event
a9 = (V.dispatch (K.serverStep (E.run (S.acceptedFork (ident 60) (Shared.admission A.key₀ (ident 60) (ident 61) 10)))))
s9 : V.Runtime
s9 = snapshot (after a9 s8)
e9 : V.advance a9 s8 ≡ just s9
e9 = refl

a10 : V.Event
a10 = (V.dispatch (K.serverStep (E.run (admit (ident 60) Admission.take))))
s10 : V.Runtime
s10 = snapshot (after a10 s9)
e10 : V.advance a10 s9 ≡ just s10
e10 = refl

a11 : V.Event
a11 = (V.dispatch (K.serverStep (E.run (admit (ident 60) Admission.countLimit))))
s11 : V.Runtime
s11 = snapshot (after a11 s10)
e11 : V.advance a11 s10 ≡ just s11
e11 = refl

a12 : V.Event
a12 = (V.dispatch (K.serverStep (E.run (admit (ident 60) Admission.allocatePromise))))
s12 : V.Runtime
s12 = snapshot (after a12 s11)
e12 : V.advance a12 s11 ≡ just s12
e12 = refl

actions : List V.Event
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ []

final : V.Runtime
final = s12

abstract
  path : V.Runs s0 actions final
  path = V.more e1 (V.more e2 (V.more e3 (V.more e4 (V.more e5 (V.more e6 (V.more e7 (V.more e8 (V.more e9 (V.more e10 (V.more e11 (V.more e12 (V.stop))))))))))))

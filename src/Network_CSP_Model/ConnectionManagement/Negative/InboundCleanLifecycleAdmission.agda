{-# OPTIONS --guardedness #-}

-- All states below are normalized actual successors; every edge is refl.
module ConnectionManagement.Negative.InboundCleanLifecycleAdmission where

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

s0 : V.Runtime
s0 = initial

a1 : V.Event
a1 = (V.dispatch (K.serverStep (E.run (S.acceptedFork A.w₀ F.r₀))))
s1 : V.Runtime
s1 = snapshot (after a1 s0)
e1 : V.advance a1 s0 ≡ just s1
e1 = refl

a2 : V.Event
a2 = (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.take))))
s2 : V.Runtime
s2 = snapshot (after a2 s1)
e2 : V.advance a2 s1 ≡ just s2
e2 = refl

a3 : V.Event
a3 = (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.countLimit))))
s3 : V.Runtime
s3 = snapshot (after a3 s2)
e3 : V.advance a3 s2 ≡ just s3
e3 = refl

a4 : V.Event
a4 = (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.allocatePromise))))
s4 : V.Runtime
s4 = snapshot (after a4 s3)
e4 : V.advance a4 s3 ≡ just s4
e4 = refl

a5 : V.Event
a5 = (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.chooseEntry))))
s5 : V.Runtime
s5 = snapshot (after a5 s4)
e5 : V.advance a5 s4 ≡ just s5
e5 = refl

a6 : V.Event
a6 = (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.fork))))
s6 : V.Runtime
s6 = snapshot (after a6 s5)
e6 : V.advance a6 s5 ≡ just s6
e6 = refl

a7 : V.Event
a7 = (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.putMapBack))))
s7 : V.Runtime
s7 = snapshot (after a7 s6)
e7 : V.advance a7 s6 ≡ just s7
e7 = refl

a8 : V.Event
a8 = (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.readCounters))))
s8 : V.Runtime
s8 = snapshot (after a8 s7)
e8 : V.advance a8 s7 ≡ just s8
e8 = refl

a9 : V.Event
a9 = (V.dispatch (K.serverStep (E.run (handler (H.enterHandshake A.child₀)))))
s9 : V.Runtime
s9 = snapshot (after a9 s8)
e9 : V.advance a9 s8 ≡ just s9
e9 = refl

a10 : V.Event
a10 = (V.dispatch (K.serverStep (E.run (mux (U.negotiate A.child₀ I.ps duplex)))))
s10 : V.Runtime
s10 = snapshot (after a10 s9)
e10 : V.advance a10 s9 ≡ just s10
e10 = refl

a11 : V.Event
a11 = (V.dispatch (K.serverStep (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0))))))
s11 : V.Runtime
s11 = snapshot (after a11 s10)
e11 : V.advance a11 s10 ≡ just s11
e11 = refl

a12 : V.Event
a12 = (V.dispatch (K.serverStep (E.run (mux (U.publishSuccess A.child₀)))))
s12 : V.Runtime
s12 = snapshot (after a12 s11)
e12 : V.advance a12 s11 ≡ just s12
e12 = refl

a13 : V.Event
a13 = (V.dispatch (K.serverStep (E.run (consume Handshake.readResult))))
s13 : V.Runtime
s13 = snapshot (after a13 s12)
e13 : V.advance a13 s12 ≡ just s13
e13 = refl

a14 : V.Event
a14 = (V.dispatch (K.serverStep (E.run (consume Handshake.commitResult))))
s14 : V.Runtime
s14 = snapshot (after a14 s13)
e14 : V.advance a14 s13 ≡ just s14
e14 = refl

a15 : V.Event
a15 = (V.dispatch (K.serverStep (E.run (consume Handshake.readResultCounters))))
s15 : V.Runtime
s15 = snapshot (after a15 s14)
e15 : V.advance a15 s14 ≡ just s15
e15 = refl

a16 : V.Event
a16 = (V.dispatch (K.serverStep (E.run (consume Handshake.enqueueInbound))))
s16 : V.Runtime
s16 = snapshot (after a16 s15)
e16 : V.advance a16 s15 ≡ just s16
e16 = refl

a17 : V.Event
a17 = (V.dispatch (K.serverStep (E.run (consume Handshake.returnResult))))
s17 : V.Runtime
s17 = snapshot (after a17 s16)
e17 : V.advance a17 s16 ≡ just s17
e17 = refl

a18 : V.Event
a18 = (V.dispatch (K.serverStep (E.run (S.workerReturned A.w₀))))
s18 : V.Runtime
s18 = snapshot (after a18 s17)
e18 : V.advance a18 s17 ≡ just s18
e18 = refl

a19 : V.Event
a19 = (V.dispatch (K.serverStep (E.run (S.workerResult A.w₀))))
s19 : V.Runtime
s19 = snapshot (after a19 s18)
e19 : V.advance a19 s18 ≡ just s19
e19 = refl

a20 : V.Event
a20 = ig (IG.captureTime 10)
s20 : V.Runtime
s20 = snapshot (after a20 s19)
e20 : V.advance a20 s19 ≡ just s20
e20 = refl

a21 : V.Event
a21 = ig IG.registerInactivity
s21 : V.Runtime
s21 = snapshot (after a21 s20)
e21 : V.advance a21 s20 ≡ just s21
e21 = refl

a22 : V.Event
a22 = ig IG.selectBatch
s22 : V.Runtime
s22 = snapshot (after a22 s21)
e22 : V.advance a22 s21 ≡ just s22
e22 = refl

a23 : V.Event
a23 = ig IG.readEvent
s23 : V.Runtime
s23 = snapshot (after a23 s22)
e23 : V.advance a23 s22 ≡ just s23
e23 = refl

a24 : V.Event
a24 = ig IG.registerIdleTimer
s24 : V.Runtime
s24 = snapshot (after a24 s23)
e24 : V.advance a24 s23 ≡ just s24
e24 = refl

a25 : V.Event
a25 = ig IG.runResponders
s25 : V.Runtime
s25 = snapshot (after a25 s24)
e25 : V.advance a25 s24 ≡ just s25
e25 = refl

a26 : V.Event
a26 = ig IG.finishBatch
s26 : V.Runtime
s26 = snapshot (after a26 s25)
e26 : V.advance a26 s25 ≡ just s26
e26 = refl

a27 : V.Event
a27 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.allocateBuffer)))))
s27 : V.Runtime
s27 = snapshot (after a27 s26)
e27 : V.advance a27 s26 ≡ just s27
e27 = refl

a28 : V.Event
a28 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.createBearer)))))
s28 : V.Runtime
s28 = snapshot (after a28 s27)
e28 : V.advance a28 s27 ≡ just s28
e28 = refl

a29 : V.Event
a29 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.enterRun)))))
s29 : V.Runtime
s29 = snapshot (after a29 s28)
e29 : V.advance a29 s28 ≡ just s29
e29 = refl

a30 : V.Event
a30 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.traceStarting)))))
s30 : V.Runtime
s30 = snapshot (after a30 s29)
e30 : V.advance a30 s29 ≡ just s30
e30 = refl

a31 : V.Event
a31 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.allocateEgress)))))
s31 : V.Runtime
s31 = snapshot (after a31 s30)
e31 : V.advance a31 s30 ≡ just s31
e31 = refl

a32 : V.Event
a32 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.openPool)))))
s32 : V.Runtime
s32 = snapshot (after a32 s31)
e32 : V.advance a32 s31 ≡ just s32
e32 = refl

a33 : V.Event
a33 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ (T.forkMuxer (ident 0)))))))
s33 : V.Runtime
s33 = snapshot (after a33 s32)
e33 : V.advance a33 s32 ≡ just s33
e33 = refl

a34 : V.Event
a34 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.registerMuxer)))))
s34 : V.Runtime
s34 = snapshot (after a34 s33)
e34 : V.advance a34 s33 ≡ just s34
e34 = refl

a35 : V.Event
a35 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ (T.forkDemuxer (ident 1)))))))
s35 : V.Runtime
s35 = snapshot (after a35 s34)
e35 : V.advance a35 s34 ≡ just s35
e35 = refl

a36 : V.Event
a36 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.registerDemuxer)))))
s36 : V.Runtime
s36 = snapshot (after a36 s35)
e36 : V.advance a36 s35 ≡ just s36
e36 = refl

a37 : V.Event
a37 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.traceMature)))))
s37 : V.Runtime
s37 = snapshot (after a37 s36)
e37 : V.advance a37 s36 ≡ just s37
e37 = refl

a38 : V.Event
a38 = (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.enterMonitor)))))
s38 : V.Runtime
s38 = snapshot (after a38 s37)
e38 : V.advance a38 s37 ≡ just s38
e38 = refl

actions : List V.Event
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ a19 ∷ a20 ∷ a21 ∷ a22 ∷ a23 ∷ a24 ∷ a25 ∷ a26 ∷ a27 ∷ a28 ∷ a29 ∷ a30 ∷ a31 ∷ a32 ∷ a33 ∷ a34 ∷ a35 ∷ a36 ∷ a37 ∷ a38 ∷ []

abstract
  path : V.Runs s0 actions s38
  path = V.more e1 (V.more e2 (V.more e3 (V.more e4 (V.more e5 (V.more e6 (V.more e7 (V.more e8 (V.more e9 (V.more e10 (V.more e11 (V.more e12 (V.more e13 (V.more e14 (V.more e15 (V.more e16 (V.more e17 (V.more e18 (V.more e19 (V.more e20 (V.more e21 (V.more e22 (V.more e23 (V.more e24 (V.more e25 (V.more e26 (V.more e27 (V.more e28 (V.more e29 (V.more e30 (V.more e31 (V.more e32 (V.more e33 (V.more e34 (V.more e35 (V.more e36 (V.more e37 (V.more e38 (V.stop))))))))))))))))))))))))))))))))))))))

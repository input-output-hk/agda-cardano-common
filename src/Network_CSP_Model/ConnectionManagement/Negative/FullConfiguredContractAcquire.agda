{-# OPTIONS --guardedness #-}

module ConnectionManagement.Negative.FullConfiguredContractAcquire where

open import ConnectionManagement.Negative.FullConfiguredProfile
import ConnectionManagement.ConfiguredProtocols as Contracts
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.Rules.OutboundRelease as OutRelease
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.MuxJobTypes as JobTypes
import ConnectionManagement.ProtocolContracts as C1
import ConnectionManagement.ProtocolContracts2 as C2
import ConnectionManagement.ProtocolContracts3 as C3
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.Negative.FullConfiguredAcquire as A
import ConnectionManagement.Negative.FullConfiguredBlocked as D

wrap : V.Runtime → B.State
wrap s = B.initial s L.child (ident 0) (ident 0)

s0 : B.State
s0 = wrap initial

a1 : B.Action
a1 = B.run (A.a1)
s1 : B.State
s1 = wrap A.s1
e1 : B.step a1 s0 ≡ just s1
e1 = refl

a2 : B.Action
a2 = B.run (A.a2)
s2 : B.State
s2 = wrap A.s2
e2 : B.step a2 s1 ≡ just s2
e2 = refl

a3 : B.Action
a3 = B.run (A.a3)
s3 : B.State
s3 = wrap A.s3
e3 : B.step a3 s2 ≡ just s3
e3 = refl

a4 : B.Action
a4 = B.run (A.a4)
s4 : B.State
s4 = wrap A.s4
e4 : B.step a4 s3 ≡ just s4
e4 = refl

a5 : B.Action
a5 = B.run (A.a5)
s5 : B.State
s5 = wrap A.s5
e5 : B.step a5 s4 ≡ just s5
e5 = refl

a6 : B.Action
a6 = B.run (A.a6)
s6 : B.State
s6 = wrap A.s6
e6 : B.step a6 s5 ≡ just s6
e6 = refl

a7 : B.Action
a7 = B.run (A.a7)
s7 : B.State
s7 = wrap A.s7
e7 : B.step a7 s6 ≡ just s7
e7 = refl

a8 : B.Action
a8 = B.run (A.a8)
s8 : B.State
s8 = wrap A.s8
e8 : B.step a8 s7 ≡ just s8
e8 = refl

a9 : B.Action
a9 = B.run (A.a9)
s9 : B.State
s9 = wrap A.s9
e9 : B.step a9 s8 ≡ just s9
e9 = refl

a10 : B.Action
a10 = B.run (A.a10)
s10 : B.State
s10 = wrap A.s10
e10 : B.step a10 s9 ≡ just s10
e10 = refl

a11 : B.Action
a11 = B.run (A.a11)
s11 : B.State
s11 = wrap A.s11
e11 : B.step a11 s10 ≡ just s11
e11 = refl

a12 : B.Action
a12 = B.run (A.a12)
s12 : B.State
s12 = wrap A.s12
e12 : B.step a12 s11 ≡ just s12
e12 = refl

a13 : B.Action
a13 = B.run (A.a13)
s13 : B.State
s13 = wrap A.s13
e13 : B.step a13 s12 ≡ just s13
e13 = refl

a14 : B.Action
a14 = B.run (A.a14)
s14 : B.State
s14 = wrap A.s14
e14 : B.step a14 s13 ≡ just s14
e14 = refl

a15 : B.Action
a15 = B.run (A.a15)
s15 : B.State
s15 = wrap A.s15
e15 : B.step a15 s14 ≡ just s15
e15 = refl

a16 : B.Action
a16 = B.run (A.a16)
s16 : B.State
s16 = wrap A.s16
e16 : B.step a16 s15 ≡ just s16
e16 = refl

a17 : B.Action
a17 = B.run (A.a17)
s17 : B.State
s17 = wrap A.s17
e17 : B.step a17 s16 ≡ just s17
e17 = refl

a18 : B.Action
a18 = B.run (A.a18)
s18 : B.State
s18 = wrap A.s18
e18 : B.step a18 s17 ≡ just s18
e18 = refl

a19 : B.Action
a19 = B.run (A.a19)
s19 : B.State
s19 = wrap A.s19
e19 : B.step a19 s18 ≡ just s19
e19 = refl

a20 : B.Action
a20 = B.run (A.a20)
s20 : B.State
s20 = wrap A.s20
e20 : B.step a20 s19 ≡ just s20
e20 = refl

a21 : B.Action
a21 = B.run (A.a21)
s21 : B.State
s21 = wrap A.s21
e21 : B.step a21 s20 ≡ just s21
e21 = refl

a22 : B.Action
a22 = B.run (A.a22)
s22 : B.State
s22 = wrap A.s22
e22 : B.step a22 s21 ≡ just s22
e22 = refl

a23 : B.Action
a23 = B.run (A.a23)
s23 : B.State
s23 = wrap A.s23
e23 : B.step a23 s22 ≡ just s23
e23 = refl

a24 : B.Action
a24 = B.run (D.negotiate)
s24 : B.State
s24 = wrap D.endpoint
e24 : B.step a24 s23 ≡ just s24
e24 = refl

a25 : B.Action
a25 = B.run (server (E.run (mux (U.allocateHandle L.child (ident 0) (ident 0)))))
s25 : B.State
s25 = wrap D.allocated
e25 : B.step a25 s24 ≡ just s25
e25 = refl

actions : List B.Action
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ a13 ∷ a14 ∷ a15 ∷ a16 ∷ a17 ∷ a18 ∷ a19 ∷ a20 ∷ a21 ∷ a22 ∷ a23 ∷ a24 ∷ a25 ∷ []

abstract
  path : B.Runs s0 actions s25
  path = B.more e1 ( B.more e2 ( B.more e3 ( B.more e4 ( B.more e5 ( B.more e6 ( B.more e7 ( B.more e8 ( B.more e9 ( B.more e10 ( B.more e11 ( B.more e12 ( B.more e13 ( B.more e14 ( B.more e15 ( B.more e16 ( B.more e17 ( B.more e18 ( B.more e19 ( B.more e20 ( B.more e21 ( B.more e22 ( B.more e23 ( B.more e24 ( B.more e25 (B.done)))))))))))))))))))))))))

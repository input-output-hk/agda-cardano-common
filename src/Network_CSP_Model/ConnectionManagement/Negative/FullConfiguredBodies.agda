{-# OPTIONS --guardedness #-}

-- Each snapshot is the normalized successor of one independently checked edge.
module ConnectionManagement.Negative.FullConfiguredBodies where

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
import ConnectionManagement.Negative.FullConfiguredDemote as Prefix

afterContract : B.Action → B.State → B.State
afterContract a s with B.step a s
... | just t = t
... | nothing = s

s0 : B.State
s0 = Prefix.s18

a1 : B.Action
a1 = B.contract2 (C2.ready C2.keepClient)
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

a2 : B.Action
a2 = B.contract1 C1.contextReady
s2 : B.State
s2 = snapshot (afterContract a2 s1)
e2 : B.step a2 s1 ≡ just s2
e2 = refl

a3 : B.Action
a3 = B.contract1 C1.keepAliveReady
s3 : B.State
s3 = snapshot (afterContract a3 s2)
e3 : B.step a3 s2 ≡ just s3
e3 = refl

a4 : B.Action
a4 = B.contract1 C1.registerSync
s4 : B.State
s4 = snapshot (afterContract a4 s3)
e4 : B.step a4 s3 ≡ just s4
e4 = refl

a5 : B.Action
a5 = B.contract1 C1.registerFetch
s5 : B.State
s5 = snapshot (afterContract a5 s4)
e5 : B.step a5 s4 ≡ just s5
e5 = refl

a6 : B.Action
a6 = B.contract1 C1.rendezvous
s6 : B.State
s6 = snapshot (afterContract a6 s5)
e6 : B.step a6 s5 ≡ just s6
e6 = refl

a7 : B.Action
a7 = B.contract1 C1.enterCandidate
s7 : B.State
s7 = snapshot (afterContract a7 s6)
e7 : B.step a7 s6 ≡ just s7
e7 = refl

a8 : B.Action
a8 = B.contract3 (C3.start C3.chainClient)
s8 : B.State
s8 = snapshot (afterContract a8 s7)
e8 : B.step a8 s7 ≡ just s8
e8 = refl

a9 : B.Action
a9 = B.contract2 (C2.start C2.txClient)
s9 : B.State
s9 = snapshot (afterContract a9 s8)
e9 : B.step a9 s8 ≡ just s9
e9 = refl

a10 : B.Action
a10 = B.contract3 (C3.start C3.notifyClient)
s10 : B.State
s10 = snapshot (afterContract a10 s9)
e10 : B.step a10 s9 ≡ just s10
e10 = refl

a11 : B.Action
a11 = B.contract3 (C3.start C3.fetchClient)
s11 : B.State
s11 = snapshot (afterContract a11 s10)
e11 : B.step a11 s10 ≡ just s11
e11 = refl

a12 : B.Action
a12 = B.contract3 C3.account
s12 : B.State
s12 = snapshot (afterContract a12 s11)
e12 : B.step a12 s11 ≡ just s12
e12 = refl

actions : List B.Action
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ a9 ∷ a10 ∷ a11 ∷ a12 ∷ []

abstract
  path : B.Runs s0 actions s12
  path = B.more e1 ( B.more e2 ( B.more e3 ( B.more e4 ( B.more e5 ( B.more e6 ( B.more e7 ( B.more e8 ( B.more e9 ( B.more e10 ( B.more e11 ( B.more e12 (B.done))))))))))))

{-# OPTIONS --guardedness #-}

-- Each snapshot is the normalized successor of one independently checked edge.
module ConnectionManagement.Negative.FullConfiguredHot2 where

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
import ConnectionManagement.Negative.FullConfiguredPromote as Prefix

afterContract : B.Action → B.State → B.State
afterContract a s with B.step a s
... | just t = t
... | nothing = s

s0 : B.State
s0 = Prefix.s21

a1 : B.Action
a1 = B.run (V.startNext (ident 2) (ident 11))
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

a2 : B.Action
a2 = B.run (V.selectStart L.child)
s2 : B.State
s2 = snapshot (afterContract a2 s1)
e2 : B.step a2 s1 ≡ just s2
e2 = refl

a3 : B.Action
a3 = B.run (V.invokeStartTrace L.child)
s3 : B.State
s3 = snapshot (afterContract a3 s2)
e3 : B.step a3 s2 ≡ just s3
e3 = refl

a4 : B.Action
a4 = B.run (V.returnStartTrace L.child)
s4 : B.State
s4 = snapshot (afterContract a4 s3)
e4 : B.step a4 s3 ≡ just s4
e4 = refl

a5 : B.Action
a5 = B.run (V.forkStart L.child (ident 11))
s5 : B.State
s5 = snapshot (afterContract a5 s4)
e5 : B.step a5 s4 ≡ just s5
e5 = refl

a6 : B.Action
a6 = B.run (V.registerStart (ident 11))
s6 : B.State
s6 = snapshot (afterContract a6 s5)
e6 : B.step a6 s5 ≡ just s6
e6 = refl

a7 : B.Action
a7 = B.run (protocol (P.enterProtocolBody (ident 11)))
s7 : B.State
s7 = snapshot (afterContract a7 s6)
e7 : B.step a7 s6 ≡ just s7
e7 = refl

a8 : B.Action
a8 = B.capture 2 (ident 11)
s8 : B.State
s8 = snapshot (afterContract a8 s7)
e8 : B.step a8 s7 ≡ just s8
e8 = refl

actions : List B.Action
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ a7 ∷ a8 ∷ []

abstract
  path : B.Runs s0 actions s8
  path = B.more e1 ( B.more e2 ( B.more e3 ( B.more e4 ( B.more e5 ( B.more e6 ( B.more e7 ( B.more e8 (B.done))))))))

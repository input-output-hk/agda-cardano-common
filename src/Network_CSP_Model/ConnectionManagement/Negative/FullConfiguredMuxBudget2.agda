{-# OPTIONS --guardedness #-}

-- Each snapshot is the normalized successor of one independently checked edge.
module ConnectionManagement.Negative.FullConfiguredMuxBudget2 where

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
import ConnectionManagement.Negative.FullConfiguredMuxBudget2Edge0 as Prefix

afterContract : B.Action → B.State → B.State
afterContract a s with B.step a s
... | just t = t
... | nothing = s

s0 : B.State
s0 = Prefix.s1

a1 : B.Action
a1 = B.run (protocol (P.asyncInfraResult L.child JobTypes.muxer))
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

actions : List B.Action
actions = a1 ∷ []

abstract
  path : B.Runs s0 actions s1
  path = B.more e1 (B.done)

-- Preserve the original final checkpoint name.
s2 : B.State
s2 = s1

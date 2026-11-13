{-# OPTIONS --guardedness #-}

-- Both monitor bodies/results finish after their independent Cold observations.
module ConnectionManagement.Negative.ConcurrentLifecycle19 where

open import ConnectionManagement.Negative.ConcurrentLifecycleSupport
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

import ConnectionManagement.Rules.MuxJobTypes as JobTypes

import ConnectionManagement.Negative.ConcurrentLifecycle18 as Prefix

s0 : V.Runtime
s0 = Prefix.final

a1 : V.Event
a1 = peer (PS.finishMonitor (ident 50))
s1 : V.Runtime
s1 = snapshot (after a1 s0)
e1 : V.advance a1 s0 ≡ just s1
e1 = refl

a2 : V.Event
a2 = peer (PS.deregisterMonitor (ident 50))
s2 : V.Runtime
s2 = snapshot (after a2 s1)
e2 : V.advance a2 s1 ≡ just s2
e2 = refl

a3 : V.Event
a3 = peer (PS.publishMonitorResult (ident 50))
s3 : V.Runtime
s3 = snapshot (after a3 s2)
e3 : V.advance a3 s2 ≡ just s3
e3 = refl

a4 : V.Event
a4 = peer (PS.finishMonitor (ident 51))
s4 : V.Runtime
s4 = snapshot (after a4 s3)
e4 : V.advance a4 s3 ≡ just s4
e4 = refl

a5 : V.Event
a5 = peer (PS.deregisterMonitor (ident 51))
s5 : V.Runtime
s5 = snapshot (after a5 s4)
e5 : V.advance a5 s4 ≡ just s5
e5 = refl

a6 : V.Event
a6 = peer (PS.publishMonitorResult (ident 51))
s6 : V.Runtime
s6 = snapshot (after a6 s5)
e6 : V.advance a6 s5 ≡ just s6
e6 = refl

actions : List V.Event
actions = a1 ∷ a2 ∷ a3 ∷ a4 ∷ a5 ∷ a6 ∷ []

final : V.Runtime
final = s6

abstract
  path : V.Runs s0 actions final
  path = V.more e1 (V.more e2 (V.more e3 (V.more e4 (V.more e5 (V.more e6 (V.stop))))))

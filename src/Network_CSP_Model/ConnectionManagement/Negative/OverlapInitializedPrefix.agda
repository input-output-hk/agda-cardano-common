{-# OPTIONS --guardedness #-}

-- Reuse only the genuine initialized prefix; leave its TIME_WAIT finally pending.
module ConnectionManagement.Negative.OverlapInitializedPrefix where

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

actions : List V.Event
actions = Old.schedule ++ (Old.a10 ∷ Old.a11 ∷ Old.a12 ∷ Old.a13 ∷ Old.a14 ∷ Old.a15 ∷ Old.a16 ∷ Old.a17 ∷ Old.a18 ∷ Old.a19 ∷ Old.a20 ∷ [])

final : V.Runtime
final = Old.s20

abstract
  path : V.Runs initial actions final
  path = Old.append Old.initialized-to-obstruction (V.more Old.e10 (V.more Old.e11 (V.more Old.e12 (V.more Old.e13 (V.more Old.e14 (V.more Old.e15 (V.more Old.e16 (V.more Old.e17 (V.more Old.e18 (V.more Old.e19 (V.more Old.e20 (V.stop))))))))))))

step-count : length actions ≡ 105
step-count = refl

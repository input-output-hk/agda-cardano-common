{-# OPTIONS --guardedness #-}

-- Normalized single-edge successors; each accepted edge is independently refl.
module ConnectionManagement.Negative.InboundConfiguredMux5Edge1 where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Scenarios.Admission as A

import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Negative.InboundConfiguredMux5Edge0 as Prefix

s0 : B.State
s0 = Prefix.s1

a1 : B.Action
a1 = B.run (protocol (P.deregisterInfra A.child₀ Types.demuxer))
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

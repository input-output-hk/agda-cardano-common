{-# OPTIONS --guardedness #-}

-- Normalized single-edge successors; each accepted edge is independently refl.
module ConnectionManagement.Negative.InboundConfiguredCleanup4Edge0 where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Scenarios.Admission as A

import ConnectionManagement.Negative.InboundConfiguredCleanup3 as Prefix

s0 : B.State
s0 = Prefix.s3

a1 : B.Action
a1 = B.run (exit (W.cleanup A.child₀ Cleanup.takeCleanupMap))
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

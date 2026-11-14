{-# OPTIONS --guardedness #-}

-- Normalized single-edge successors; each accepted edge is independently refl.
module ConnectionManagement.Negative.InboundConfiguredCleanup1Edge0 where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Rules.IGRegistration as IG

import ConnectionManagement.Negative.InboundConfiguredCleanup0 as Prefix

s0 : B.State
s0 = Prefix.s3

a1 : B.Action
a1 = B.run (ig IG.selectBatch)
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

{-# OPTIONS --guardedness #-}

-- Normalized single-edge successors; each accepted edge is independently refl.
module ConnectionManagement.Negative.InboundConfiguredChainResult3 where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Scenarios.Admission as A

import ConnectionManagement.Negative.InboundConfiguredChainResult2 as Prefix

s0 : B.State
s0 = Prefix.s3

a1 : B.Action
a1 = B.run (group (G.run (M.commitTracer A.child₀)))
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

a2 : B.Action
a2 = B.run (delta (N.D.beginDeltaQ A.child₀))
s2 : B.State
s2 = snapshot (afterContract a2 s1)
e2 : B.step a2 s1 ≡ just s2
e2 = refl

a3 : B.Action
a3 = B.run (delta (N.D.observeReturn A.child₀))
s3 : B.State
s3 = snapshot (afterContract a3 s2)
e3 : B.step a3 s2 ≡ just s3
e3 = refl

actions : List B.Action
actions = a1 ∷ a2 ∷ a3 ∷ []

abstract
  path : B.Runs s0 actions s3
  path = B.more e1 (B.more e2 (B.more e3 (B.done)))

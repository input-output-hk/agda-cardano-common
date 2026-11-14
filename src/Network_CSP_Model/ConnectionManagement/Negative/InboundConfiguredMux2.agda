{-# OPTIONS --guardedness #-}

-- Compose separately checked refl edges without repeating their normalization.
module ConnectionManagement.Negative.InboundConfiguredMux2 where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport

import ConnectionManagement.Negative.InboundConfiguredMux1 as Prefix

import ConnectionManagement.Negative.InboundConfiguredMux2Edge0 as E0
import ConnectionManagement.Negative.InboundConfiguredMux2Edge1 as E1
import ConnectionManagement.Negative.InboundConfiguredMux2Edge2 as E2

s0 : B.State
s0 = Prefix.s3

a1 : B.Action
a1 = E0.a1
s1 : B.State
s1 = E0.s1
e1 : B.step a1 s0 ≡ just s1
e1 = E0.e1

a2 : B.Action
a2 = E1.a1
s2 : B.State
s2 = E1.s1
e2 : B.step a2 s1 ≡ just s2
e2 = E1.e1

a3 : B.Action
a3 = E2.a1
s3 : B.State
s3 = E2.s1
e3 : B.step a3 s2 ≡ just s3
e3 = E2.e1

actions : List B.Action
actions = a1 ∷ a2 ∷ a3 ∷ []

abstract
  path : B.Runs s0 actions s3
  path = B.more e1 (B.more e2 (B.more e3 (B.done)))

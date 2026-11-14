{-# OPTIONS --guardedness #-}

-- Normalized single-edge successors; each accepted edge is independently refl.
module ConnectionManagement.Negative.InboundConfiguredStart17 where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport

import ConnectionManagement.Negative.InboundConfiguredStart16 as Prefix

s0 : B.State
s0 = Prefix.s3

a1 : B.Action
a1 = B.run (protocol (P.enterProtocolBody (ident 15)))
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

a2 : B.Action
a2 = B.capture 19 (ident 15)
s2 : B.State
s2 = snapshot (afterContract a2 s1)
e2 : B.step a2 s1 ≡ just s2
e2 = refl

actions : List B.Action
actions = a1 ∷ a2 ∷ []

abstract
  path : B.Runs s0 actions s2
  path = B.more e1 (B.more e2 (B.done))

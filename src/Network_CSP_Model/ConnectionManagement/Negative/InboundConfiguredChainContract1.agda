{-# OPTIONS --guardedness #-}

-- Normalized single-edge successors; each accepted edge is independently refl.
module ConnectionManagement.Negative.InboundConfiguredChainContract1 where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport

import ConnectionManagement.ProtocolContracts as C1
import ConnectionManagement.Negative.InboundConfiguredChainContract0 as Prefix

s0 : B.State
s0 = Prefix.s3

a1 : B.Action
a1 = B.contract1 (C1.peerDone C1.chainServer)
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

a2 : B.Action
a2 = B.contract1 (C1.serverCleanup C1.chainServer)
s2 : B.State
s2 = snapshot (afterContract a2 s1)
e2 : B.step a2 s1 ≡ just s2
e2 = refl

actions : List B.Action
actions = a1 ∷ a2 ∷ []

abstract
  path : B.Runs s0 actions s2
  path = B.more e1 (B.more e2 (B.done))

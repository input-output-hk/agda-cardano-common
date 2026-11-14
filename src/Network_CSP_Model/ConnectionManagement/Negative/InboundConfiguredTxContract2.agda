{-# OPTIONS --guardedness #-}

-- Normalized single-edge successors; each accepted edge is independently refl.
module ConnectionManagement.Negative.InboundConfiguredTxContract2 where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport

import ConnectionManagement.ProtocolContracts2 as C2
import ConnectionManagement.Negative.InboundConfiguredTxContract1 as Prefix

s0 : B.State
s0 = Prefix.s3

a1 : B.Action
a1 = B.contract2 (C2.cleanup C2.txServerV2)
s1 : B.State
s1 = snapshot (afterContract a1 s0)
e1 : B.step a1 s0 ≡ just s1
e1 = refl

actions : List B.Action
actions = a1 ∷ []

abstract
  path : B.Runs s0 actions s1
  path = B.more e1 (B.done)

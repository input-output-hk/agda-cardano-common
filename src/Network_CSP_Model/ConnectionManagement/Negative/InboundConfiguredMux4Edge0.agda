{-# OPTIONS --guardedness #-}

-- Normalized single-edge successors; each accepted edge is independently refl.
module ConnectionManagement.Negative.InboundConfiguredMux4Edge0 where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport


import ConnectionManagement.Negative.InboundConfiguredMux4Edge0State as Value

s0 : B.State
s0 = Value.s0

a1 : B.Action
a1 = Value.a1
s1 : B.State
s1 = Value.s1
e1 : B.step a1 s0 ≡ just s1
e1 = refl

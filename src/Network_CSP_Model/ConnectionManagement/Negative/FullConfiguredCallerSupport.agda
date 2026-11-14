{-# OPTIONS --guardedness #-}

-- Concrete-schedule caller certification without the reserved global safety
-- proof closure. The executable variant and its Allowed predicate are reused.
module ConnectionManagement.Negative.FullConfiguredCallerSupport where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import Data.List using (map)
open import Data.Bool using (_∧_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Variants.OwnedCallers as Variant
import ConnectionManagement.Properties.PoolRelays as Proof
import ConnectionManagement.Rules.PoolRelays as RR
module Owned = Variant.Protocols I.bearerClosed classify capability
module Outer = Owned.Outer
module Cert = Proof.Certified V.advance Outer.runtimeReturned

outerOnly : Outer.OuterAction → Bool
outerOnly (Outer.innerAct a) = Owned.eventOnly a
outerOnly (Outer.relaysAct _) = true
everyOwned : List Outer.OuterAction → Bool
everyOwned [] = true
everyOwned (a ∷ as) = outerOnly a ∧ everyOwned as


{-# OPTIONS --guardedness #-}

-- Certify the entire initialized concurrency history in the executable production
-- caller design. Policy examines actual selected plans, including complete.
module ConnectionManagement.Negative.ConcurrentLifecycleOwnedCallers where

open import ConnectionManagement.Negative.ConcurrentLifecycleSupport
open import Data.List using (map)
import ConnectionManagement.Negative.ConcurrentLifecycles as Run
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Variants.OwnedCallers as Variant
import ConnectionManagement.Properties.OwnedCallers as Policy
import ConnectionManagement.Properties.PoolRelays as Proof
import ConnectionManagement.Rules.PoolRelays as RR

module Owned = Variant.Protocols I.bearerClosed classify capability
module PolicyCheck = Policy.Protocols I.bearerClosed classify capability
module Outer = Owned.Outer
module Cert = Proof.Certified V.advance Outer.runtimeReturned

-- Lift an unchanged frontend execution inside the actual outer relays scope.
lift : ∀ {i as i′} t → V.Runs i as i′ →
  Outer.Executes (Outer.outer i (RR.relaysState t RR.inside))
    (map Outer.innerAct as) (Outer.outer i′ (RR.relaysState t RR.inside))
lift t V.stop = Outer.done
lift t (V.more {s = i} {a = a} eq rest) =
  Outer.next (Cert.lift-inner a i t eq) (lift t rest)

-- The relays remain inside: this is finite concurrency evidence, not global shutdown.
outer-schedule : List Outer.OuterAction
outer-schedule = map Outer.innerAct Run.schedule

abstract
  initialized-outer : Outer.Executes
    (Outer.outer initial (RR.initial true)) outer-schedule
    (Outer.outer Run.final (RR.initial true))
  initialized-outer = lift (just RR.running) Run.initialized-to-completion

-- No raw core begin occurs anywhere, including in the reused acquisition.
every-owned : PolicyCheck.everyOwned outer-schedule ≡ true
every-owned = refl

-- This is a semantic policy proof on the actual successful source execution.
production-policy : Owned.Allowed initialized-outer
production-policy = PolicyCheck.source-policy every-owned initialized-outer

-- The same initializer, labels, edges and endpoint execute in OwnedCallers.
production-run : Owned.OuterRuns′
  (Outer.outer initial (RR.initial true)) outer-schedule
  (Outer.outer Run.final (RR.initial true))
production-run = Owned.allowed-build initialized-outer production-policy

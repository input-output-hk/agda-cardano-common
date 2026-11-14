{-# OPTIONS --guardedness #-}

-- Whole initialized schedule under the actual executable owned-caller policy.
module ConnectionManagement.Negative.FullConfiguredCallers where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredCallerSupport using
  (module Owned; module Outer; everyOwned)
import ConnectionManagement.Negative.FullConfiguredCallerPolicy as Policy
import ConnectionManagement.Negative.FullConfiguredWitness as Run
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
open import Data.List using (map)
import ConnectionManagement.Rules.PoolRelays as RR

outer-schedule : List Outer.OuterAction
outer-schedule = map Outer.innerAct (B.erase Run.schedule)

every-owned : everyOwned outer-schedule ≡ true
every-owned = refl

abstract
  initialized-outer : Outer.Executes
    (Outer.outer initial (RR.initial true)) outer-schedule
    (Outer.outer (B.runtime Run.endpoint) (RR.initial true))
  initialized-outer = Policy.lift Run.initialized-frontend

  production-policy : Owned.Allowed initialized-outer
  production-policy = Policy.source-policy every-owned initialized-outer

production-run : Owned.OuterRuns′
  (Outer.outer initial (RR.initial true)) outer-schedule
  (Outer.outer (B.runtime Run.endpoint) (RR.initial true))
production-run = Owned.allowed-build initialized-outer production-policy

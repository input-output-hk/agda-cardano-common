{-# OPTIONS --guardedness #-}

-- Apply the general invariant to lifecycle/race/failure witnesses and its
-- forged-frame negative controls, without inspecting the final heaps directly.
module ConnectionManagement.Negative.SubsystemSupply where

open import Data.List.Relation.Unary.All using ([])
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.CSP.Fixtures as Fixture
import ConnectionManagement.CSP.GovernorLifecycle as Lifecycle
import ConnectionManagement.CSP.GovernorFailureLimit as Failures
import ConnectionManagement.Negative.Subsystem as Race
import ConnectionManagement.Negative.OutboundSupply as Forged
import ConnectionManagement.Properties.SubsystemCapture as Capture
import ConnectionManagement.Properties.SubsystemSupply as Supply
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)

-- The actual lifecycle fixture has no allocated entries or promises initially.
initial-bounded : SupplyBounds (I.world Fixture.start)
initial-bounded = [] , []

-- Establishment/activation/demotion/release preserve bounds by the general theorem.
lifecycle-bounded : Supply.Bounded Lifecycle.final
lifecycle-bounded = Supply.from-initial initial-bounded Lifecycle.path

-- The same theorem permits child completion before parent pool registration.
child-before-registration-bounded : Supply.Bounded (Race.held Lifecycle.c41)
child-before-registration-bounded = Supply.from-initial initial-bounded Race.racePath

-- Failure/backoff/forgetting does not invalidate the retained reservation's bound.
failure-limit-bounded : Supply.Bounded Failures.c211
failure-limit-bounded = Supply.from-initial initial-bounded Failures.path

-- General capture validity rejects the forged frame before its invalid write.
forged-certificate-rejected : ¬ Supply.Valid Forged.subBefore
forged-certificate-rejected (valid Data.List.Relation.Unary.All.∷ rest , bounded) =
  Forged.forged-capture-invalid valid

-- The newly proved bound excludes the forged post-state from initialized runs.
forged-poststate-unreachable : ∀ c s actions → SupplyBounds (I.world c) →
  ¬ Sub.Executes (Sub.initial (O.initial c) s) actions Forged.subAfter
forged-poststate-unreachable c s actions bounded path =
  Forged.after-not-bounded (Supply.from-initial bounded path)

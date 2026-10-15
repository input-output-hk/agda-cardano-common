{-# OPTIONS --guardedness #-}

-- Fresh-start reachability is essential: forged ticket phases carry no evidence.
module ConnectionManagement.Negative.OriginMonitorInvariant where

open import Data.List using ([]; _∷_)
open import Data.Product using (proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import ConnectionManagement.Rules.OriginMonitor
open import ConnectionManagement.Properties.OriginMonitorInvariant
open import ConnectionManagement.Properties.HandlerOrigin using (descriptor)
open import ConnectionManagement.CSP.OriginMonitorInvariant
open import ConnectionManagement.CSP.OriginMonitorWitness
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.Negative.OriginMonitor

-- Both phases derive their descriptor from the generic reachable-state theorem.
installed-invariant : Invariant selected installed
installed-invariant = reachable-invariant {t = selected} {c = E.forked} {as = allocate ∷ []} {s′ = installed} (next refl done) E.forked-resources
completed-invariant : Invariant selected completed
completed-invariant = reachable-invariant establish-path E.forked-resources

-- A ticket seeded before allocation does not describe an installed handle.
forged : State
forged = observed E.forked (published expected)
no-forged-invariant : ¬ Invariant selected forged
no-forged-invariant inv with descriptor (proj₂ inv)
... | ()

no-forged-reachable : ∀ {as} → ¬ Executes selected initial as forged
no-forged-reachable path = no-forged-invariant (reachable-invariant path E.forked-resources)

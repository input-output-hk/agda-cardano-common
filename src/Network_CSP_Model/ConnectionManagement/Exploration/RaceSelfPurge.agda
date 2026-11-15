{-# OPTIONS --guardedness #-}

-- Increment 78: search a reached phase-B window and the handler-registry
-- design. The source alphabet is the erasure of the common phase-B alphabet;
-- explicit join/sweep actions are additional observations in the design.
module ConnectionManagement.Exploration.RaceSelfPurge where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; _≤_; _≤?_)
import Data.Nat.Properties
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import ConnectionManagement.Exploration.Finite
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Domain using (DecEq-Id)
import ConnectionManagement.Exploration.Bounded as Bounded
import ConnectionManagement.CSP.Supervised as Bridge
import ConnectionManagement.Negative.ServerOwnedWorkersSelfPurge as F
import ConnectionManagement.Negative.ServerOwnedHandlersFixture as H
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Variants.ServerOwnedWorkers as Workers
import ConnectionManagement.Variants.ServerOwnedHandlers as Handlers
import ConnectionManagement.Properties.ServerOwnedHandlers as Properties
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Scenarios.Admission as A
module B = Bridge I.bearerClosed F.classify F.capability
module O = B.O
module W = Workers.Protocols I.bearerClosed F.classify F.capability
module HB = Handlers I.bearerClosed F.classify
module V = Handlers.Protocols I.bearerClosed F.classify F.capability
module Q = Properties.Protocols I.bearerClosed F.classify F.capability

-- Eight ordinary edges from the reached pre-close state to finished relays.
-- Depth 16 also accommodates the registry repair's fifteen-event continuation.
-- The preceding 77 edges are part of F.counterexample-run from its initializer.
actions = F.a78 ∷ F.a79 ∷ F.a80 ∷ F.a81 ∷ F.a82 ∷ F.a83 ∷ F.a84 ∷ F.a85 ∷ []
start = F.s77
end = F.s85
allocated : W.Outer → ℕ
allocated s = length (V.threads (W.inner s))
module Find = Bounded W.Outer W.OuterAction W.outerStep actions allocated

-- Flat, already checked native edges avoid replay normalization.
bounded : Find.BoundedRun 8 start actions end
bounded =
  Find.more {s = F.s77} {t = F.s78}
    (toWitness {a? = allocated F.s77 ≤? 8} tt) here F.e78
    (
    Find.more {s = F.s78} {t = F.s79}
      (toWitness {a? = allocated F.s78 ≤? 8} tt) (there here) F.e79
      (
      Find.more {s = F.s79} {t = F.s80}
        (toWitness {a? = allocated F.s79 ≤? 8} tt) (there (there here)) F.e80
        (
        Find.more {s = F.s80} {t = F.s81}
          (toWitness {a? = allocated F.s80 ≤? 8} tt) (there (there (there here))) F.e81
          (
          Find.more {s = F.s81} {t = F.s82}
            (toWitness {a? = allocated F.s81 ≤? 8} tt) (there (there (there (there here)))) F.e82
            (
            Find.more {s = F.s82} {t = F.s83}
              (toWitness {a? = allocated F.s82 ≤? 8} tt) (there (there (there (there (there here))))) F.e83
              (
              Find.more {s = F.s83} {t = F.s84}
                (toWitness {a? = allocated F.s83 ≤? 8} tt) (there (there (there (there (there (there here)))))) F.e84
                (
                Find.more {s = F.s84} {t = F.s85}
                  (toWitness {a? = allocated F.s84 ≤? 8} tt) (there (there (there (there (there (there (there here))))))) F.e85
                  (
                    Find.stop (toWitness {a? = allocated F.s85 ≤? 8} tt)))))))))
abstract
  known-candidate-found : (actions , end) ∈ Find.reach 16 8 start
  known-candidate-found = Find.reach-complete 16 {b = 8} {s = start} {as = actions} {t = end} bounded
    (toWitness {a? = length actions ≤? 16} tt)

-- Same ordinary labels, plus all events in the existing initialized repaired
-- progress run. This includes counters, actual Async publication and the sweep.
fixedActions = map H.label actions ++ H.SelfPurge.actions
fixedStart = H.SelfPurge.v77
module Fixed = Bounded V.Outer V.OuterAction V.outerStep fixedActions
  (λ s → length (V.threads (V.base (V.inner s))))
to-variant : ∀ {s as t} → Fixed.Raw.Executes s as t → V.Executes s as t
to-variant Fixed.Raw.done = V.done
to-variant (Fixed.Raw.next eq rest) = V.next eq (to-variant rest)

-- Generic invariant application stays separate from the concrete window.
abstract
  initial-gates : Q.Gates (V.inner fixedStart)
  initial-gates = refl
  initial-coverage : Q.Covered (V.inner fixedStart)
  initial-coverage = HB.register-covers (V.threads (V.base (V.inner fixedStart))) []

  no-pending-in-run : ∀ {s as t} → V.Executes s as t →
    Q.Gates (V.inner s) → Q.Covered (V.inner s) →
    Close.phase (V.coordinator (V.base (V.inner t))) ≡ Close.closed →
    ∀ w thread → lookup w (V.threads (V.base (V.inner t))) ≡ just thread →
    V.ready (V.base (V.inner t)) w ≡ false → ⊥
  no-pending-in-run {t = t} path gates coverage closed w thread present unavailable with
    Q.closed-registry (V.inner t) (Q.runs-gates path gates) closed
  ... | completed , results with trans
    (sym (Q.ready-member (V.base (V.inner t)) (V.registry (V.inner t)) w results
      (Q.runs-covered path coverage w thread present))) unavailable
  ... | ()

-- Every member is a real variant run; the generic invariant excludes the hit.
no-self-purge-candidate : ∀ {as s} → (as , s) ∈ Fixed.reach 16 8 fixedStart →
  Close.phase (V.coordinator (V.base (V.inner s))) ≡ Close.closed →
  ∀ w thread → lookup w (V.threads (V.base (V.inner s))) ≡ just thread →
  V.ready (V.base (V.inner s)) w ≡ false → ⊥
no-self-purge-candidate {as} {s} member = no-pending-in-run
  {s = fixedStart} {as = as} {t = s}
  (to-variant {s = fixedStart} {as = as} {t = s}
    (Fixed.real-run {b = 8} {s = fixedStart} {as = as} {t = s}
      (proj₂ (Fixed.reach-sound 16 8 fixedStart {as = as} {t = s} member))))
  initial-gates initial-coverage

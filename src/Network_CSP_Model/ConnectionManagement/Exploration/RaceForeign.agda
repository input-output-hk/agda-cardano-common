{-# OPTIONS --guardedness #-}

-- Increment 75: a complete initialized foreign-frame run. The engine explores
-- every ordering/repetition over these exact labels, through 1000 events and
-- the exact finite alphabet. Allocation pruning is disabled; the fixed labels
-- and finite depth still make the search finite.
module ConnectionManagement.Exploration.RaceForeign where

open import Data.Bool using (true)
open import Data.List using (List; map; _++_; length)
open import Data.Nat using (ℕ; _≤_; _≤?_; z≤n)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import ConnectionManagement.Exploration.Finite
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Domain using (DecEq-Id)
import ConnectionManagement.Exploration.Bounded as Bounded
import ConnectionManagement.CSP.Supervised as Bridge
import ConnectionManagement.Variants.OwnedCallers as Variant
import ConnectionManagement.Properties.OwnedCallers as Properties
import ConnectionManagement.Negative.ForeignCallerResidue as F
import ConnectionManagement.Negative.PoolRelays as R
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as P
open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as Shared
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.Rules.PoolRelays as RR
module B = Bridge I.bearerClosed P.classify Protocols.capability
module O = B.O
module V = Variant.Protocols I.bearerClosed P.classify Protocols.capability
module Q = Properties.Protocols I.bearerClosed P.classify Protocols.capability

start = O.outer Protocols.initial (RR.initial true)
actions = map O.innerAct F.innerActions ++ R.Initialized.closeActions
-- No allocation guard: this search is bounded by events and the exact finite
-- alphabet. The zero metric/budget deliberately keeps every reachable state.
allocated : O.Outer → ℕ
allocated _ = 0
module Find = Bounded O.Outer O.OuterAction O.outerStep actions allocated
module Fixed = Bounded O.Outer O.OuterAction V.outerStep′ actions allocated

-- Structural annotation adds coverage without normalizing dispatcher replay.
annotate : ∀ {s as t} → Find.Raw.Executes s as t → Covered as actions →
  Find.BoundedRun 0 s as t
annotate Find.Raw.done covered = Find.stop z≤n
annotate (Find.Raw.next eq rest) (member , covered) =
  Find.more z≤n member eq (annotate rest covered)
abstract
  initialized-run : Find.Raw.Executes start actions F.closed
  initialized-run = B.to-raw F.initialized-close
  depth-sufficient : length actions ≤ 1000
  depth-sufficient = toWitness {a? = length actions ≤? 1000} tt
  known-candidate-found : (actions , F.closed) ∈ Find.reach 1000 0 start
  known-candidate-found = Find.reach-complete 1000 {b = 0} {s = start} {as = actions} {t = F.closed}
    (annotate initialized-run (self-covered actions)) depth-sufficient

-- Convert every enumerated variant path to the existing policy execution type.
to-variant : ∀ {s as t} → Fixed.Raw.Executes s as t → V.OuterRuns′ s as t
to-variant Fixed.Raw.done = V.outer-done′
to-variant (Fixed.Raw.next eq rest) = V.outer-next′ eq (to-variant rest)

-- Freeze the initializer instantiation before applying the invariant to any
-- particular search member. Its source core and governor inputs remain exact.
abstract
  variant-no-frames : ∀ {as final t} → V.OuterRuns′ start as
    (O.outer final (RR.relaysState t RR.finished)) → Q.NoFrames final
  variant-no-frames {as} {final} {t} = Q.no-frames
    {c₀ = Machine.initial Shared.responderMode X.F.empty} {g = L.settings}
    {start = Protocols.initial} {scheduled = true} {as = as} {final = final} {t = t}
    Protocols.initializer

nothing-not-just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing-not-just ()

-- Every bounded member is covered, not just the counterexample schedule.
no-foreign-acquire : ∀ {as final t} →
  (as , O.outer final (RR.relaysState t RR.finished)) ∈ Fixed.reach 1000 0 start →
  ∀ w savedFrame → lookup w (CM.acquiring (B.T.sourceOf final)) ≡ just savedFrame → ⊥
no-foreign-acquire {as} {final} {t} member w savedFrame present = nothing-not-just
  (trans (sym (proj₁ (variant-no-frames {as = as} {final = final} {t = t}
    (to-variant {s = start} {as = as} {t = O.outer final (RR.relaysState t RR.finished)}
      (Fixed.real-run {b = 0} {s = start} {as = as} {t = O.outer final (RR.relaysState t RR.finished)}
        (proj₂ (Fixed.reach-sound 1000 0 start {as = as} {t = O.outer final (RR.relaysState t RR.finished)} member))))) w)) present)

no-foreign-release : ∀ {as final t} →
  (as , O.outer final (RR.relaysState t RR.finished)) ∈ Fixed.reach 1000 0 start →
  ∀ w savedFrame → lookup w (CM.releasing (B.T.sourceOf final)) ≡ just savedFrame → ⊥
no-foreign-release {as} {final} {t} member w savedFrame present = nothing-not-just
  (trans (sym (proj₂ (variant-no-frames {as = as} {final = final} {t = t}
    (to-variant {s = start} {as = as} {t = O.outer final (RR.relaysState t RR.finished)}
      (Fixed.real-run {b = 0} {s = start} {as = as} {t = O.outer final (RR.relaysState t RR.finished)}
        (proj₂ (Fixed.reach-sound 1000 0 start {as = as} {t = O.outer final (RR.relaysState t RR.finished)} member))))) w)) present)

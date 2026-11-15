{-# OPTIONS --guardedness #-}

-- The ten-event late-admission window starts at increment 73's reached
-- pre-CM state. Both searches forget schedule order and allow repetitions.
module ConnectionManagement.Exploration.RaceLate where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; length; take; filterᵇ)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Maybe using (just; nothing; fromMaybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import ConnectionManagement.Exploration.Finite
import ConnectionManagement.Exploration.Bounded as Bounded
import ConnectionManagement.Exploration.Text as Text
open import Data.Empty using (⊥)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Relation.Nullary.Decidable using (toWitness)
open import Data.Unit using (tt)
import ConnectionManagement.Negative.ServerLateAdmission as Late
import ConnectionManagement.Negative.ServerAdmission as Prefix
import ConnectionManagement.Negative.ServerOwnedWorkersSelfPurge as F
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Variants.ServerOwnedWorkers as Workers
import ConnectionManagement.Variants.ServerOwnedHandlers as Registry
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.State as Shared
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Scenarios.Admission as A
module V = Workers I.bearerClosed F.classify
module S = V.S
module E = V.E
module K = V.K

-- A shared embedding leaves the existing exit and peer context fixed. The
-- original Server prefix establishes the source boundary, independently of it.
embed : S.State → K.State
embed s = K.combined (E.igExitState s E.emptyExit) F.k₀
start = Prefix.atAfterIG S.igJoined
end = Late.late
lift : S.Action → K.Action
lift a = K.serverStep (E.run a)
actions : List S.Action
actions = S.scope S.beginCM ∷ Prefix.cmAction Close.captureSnapshot ∷
  Prefix.cmAction Close.finishTraversal ∷ Prefix.cmAction Close.finishClose ∷
  S.scope S.finishServer ∷ Late.lateActions

-- Capacity bound covers retained workers, sockets/handlers and fresh supplies.
capacity : S.State → ℕ
capacity s = length (S.workers s) ⊔ length (Shared.sockets (S.shared s)) ⊔
  length (Shared.handlers (S.shared s)) ⊔ Shared.nextPromise (S.shared s) ⊔
  Shared.nextEntry (Shared.cm (S.shared s))
module Find = Bounded S.State S.Action S.step actions capacity

-- Name the five late steps individually, keeping the known pre-close edges
-- flat. Each target is computed by the original Server dispatcher.
late1 = fromMaybe Prefix.returnedServer (Late.run (take 1 Late.lateActions) Prefix.returnedServer)
late2 = fromMaybe Prefix.returnedServer (Late.run (take 2 Late.lateActions) Prefix.returnedServer)
late3 = fromMaybe Prefix.returnedServer (Late.run (take 3 Late.lateActions) Prefix.returnedServer)
late4 = fromMaybe Prefix.returnedServer (Late.run (take 4 Late.lateActions) Prefix.returnedServer)
lateEvents = Late.lateActions
eventAt : ℕ → List S.Action → S.Action
eventAt _ [] = S.scope S.beginCM
eventAt Data.Nat.zero (a ∷ as) = a
eventAt (Data.Nat.suc n) (a ∷ as) = eventAt n as
late-edge1 : S.step (eventAt 0 lateEvents) (Prefix.returnedServer) ≡ just (late1)
late-edge1 = refl
late-edge2 : S.step (eventAt 1 lateEvents) (late1) ≡ just (late2)
late-edge2 = refl
late-edge3 : S.step (eventAt 2 lateEvents) (late2) ≡ just (late3)
late-edge3 = refl
late-edge4 : S.step (eventAt 3 lateEvents) (late3) ≡ just (late4)
late-edge4 = refl
late-edge5 : S.step (eventAt 4 lateEvents) (late4) ≡ just (end)
late-edge5 = refl

bounded : Find.BoundedRun 8 start actions end
bounded =
  Find.more {s = start} {t = Prefix.atAfterIG S.closingCM}
    (toWitness {a? = capacity (start) Data.Nat.≤? 8} tt) here Prefix.scope18
    (
    Find.more {s = Prefix.atAfterIG S.closingCM} {t = Prefix.cmReading}
      (toWitness {a? = capacity (Prefix.atAfterIG S.closingCM) Data.Nat.≤? 8} tt) (there here) Prefix.cm1
      (
      Find.more {s = Prefix.cmReading} {t = Prefix.cmWaiting}
        (toWitness {a? = capacity (Prefix.cmReading) Data.Nat.≤? 8} tt) (there (there here)) Prefix.cm2
        (
        Find.more {s = Prefix.cmWaiting} {t = Prefix.cmClosed}
          (toWitness {a? = capacity (Prefix.cmWaiting) Data.Nat.≤? 8} tt) (there (there (there here))) Prefix.cm3
          (
          Find.more {s = Prefix.cmClosed} {t = Prefix.returnedServer}
            (toWitness {a? = capacity (Prefix.cmClosed) Data.Nat.≤? 8} tt) (there (there (there (there here)))) Prefix.final
            (
            Find.more {s = Prefix.returnedServer} {t = late1}
              (toWitness {a? = capacity (Prefix.returnedServer) Data.Nat.≤? 8} tt) (there (there (there (there (there here))))) late-edge1
              (
              Find.more {s = late1} {t = late2}
                (toWitness {a? = capacity (late1) Data.Nat.≤? 8} tt) (there (there (there (there (there (there here)))))) late-edge2
                (
                Find.more {s = late2} {t = late3}
                  (toWitness {a? = capacity (late2) Data.Nat.≤? 8} tt) (there (there (there (there (there (there (there here))))))) late-edge3
                  (
                  Find.more {s = late3} {t = late4}
                    (toWitness {a? = capacity (late3) Data.Nat.≤? 8} tt) (there (there (there (there (there (there (there (there here)))))))) late-edge4
                    (
                    Find.more {s = late4} {t = end}
                      (toWitness {a? = capacity (late4) Data.Nat.≤? 8} tt) (there (there (there (there (there (there (there (there (there here))))))))) late-edge5
                      (
                        Find.stop (toWitness {a? = capacity end Data.Nat.≤? 8} tt)))))))))))
abstract
  known-candidate-found : (actions , end) ∈ Find.reach 10 8 start
  known-candidate-found = Find.reach-complete 10 {b = 8} {s = start} {as = actions} {t = end} bounded ≤-refl

-- Same Server labels embedded in the existing shared ownership variant. This
-- boundary search includes all permutations/repetitions, but no join operation.
fixedActions : List K.Action
fixedActions = map lift actions
handles : V.Ownership
handles = (A.w₀ , false) ∷ (A.w₁ , false) ∷ []
fixedStart : V.State
fixedStart = V.state (embed start) handles
module Fixed = Bounded V.State K.Action V.step′ fixedActions
  (λ s → capacity (E.base (K.server (V.source s))))

-- None of this window's actions creates a worker or changes ownership flags.
track-identity : ∀ {a} → a ∈ fixedActions → ∀ hs → V.track a hs ≡ hs
track-identity here hs = refl
track-identity (there here) hs = refl
track-identity (there (there here)) hs = refl
track-identity (there (there (there here))) hs = refl
track-identity (there (there (there (there here)))) hs = refl
track-identity (there (there (there (there (there here))))) hs = refl
track-identity (there (there (there (there (there (there here)))))) hs = refl
track-identity (there (there (there (there (there (there (there here))))))) hs = refl
track-identity (there (there (there (there (there (there (there (there here)))))))) hs = refl
track-identity (there (there (there (there (there (there (there (there (there here))))))))) hs = refl

-- A successful guarded edge retains the handles and establishes the boundary.
step-invariant : ∀ {a s t} → a ∈ fixedActions → V.step′ a s ≡ just t →
  V.owned s ≡ handles → V.owned t ≡ handles × V.boundary (V.source t) (V.owned t) ≡ true
step-invariant {a} {s} member eq owned with K.step a (V.source s)
... | nothing = case eq of λ ()
... | just b with V.boundary b (V.track a (V.owned s)) in gate
... | false = case eq of λ ()
... | true with just-injective eq
... | refl = trans (track-identity member (V.owned s)) owned , gate

invariant : ∀ {b s as t} → Fixed.BoundedRun b s as t →
  V.owned s ≡ handles → V.boundary (V.source s) (V.owned s) ≡ true →
  V.owned t ≡ handles × V.boundary (V.source t) (V.owned t) ≡ true
invariant (Fixed.stop _) owned gate = owned , gate
invariant (Fixed.more _ member eq rest) owned gate with step-invariant member eq owned
... | nextOwned , nextGate = invariant rest nextOwned nextGate

-- A returned Server would require the still-unjoined handles to be allJoined.
returned-impossible : ∀ s → V.owned s ≡ handles →
  V.boundary (V.source s) (V.owned s) ≡ true →
  S.stage (E.base (K.server (V.source s))) ≡ S.serverReturned → ⊥
returned-impossible s owned gate returned rewrite returned | owned = case gate of λ ()

no-late-candidate : ∀ {as s} → (as , s) ∈ Fixed.reach 10 8 fixedStart →
  S.stage (E.base (K.server (V.source s))) ≡ S.serverReturned → ⊥
no-late-candidate {s = s} member returned with invariant
  (proj₂ (Fixed.reach-sound 10 8 fixedStart member)) refl refl
... | owned , gate = returned-impossible s owned gate returned

-- Run the identical window in the combined handler-registry/OwnedCallers
-- dispatcher as well. The shared comparison above explains its worker gate.
module HR = Registry I.bearerClosed F.classify
module H = HR.Protocols F.capability
registryActions : List H.OuterAction
registryActions = map (λ a → H.innerAct (H.sourceEvent (H.W.run (H.T.dispatch (lift a))))) actions
registryStart : H.Outer
registryStart = H.outer
  (H.pack (H.W.runtime (H.T.runtime (embed start) H.T.empty) handles) [] HR.unread)
  (RR.initial true)
module RegistryFind = Bounded H.Outer H.OuterAction H.outerStep registryActions
  (λ s → capacity (H.server (H.base (H.inner s))))
returnedRegistry : H.Outer → Bool
returnedRegistry s with S.stage (H.server (H.base (H.inner s)))
... | S.serverReturned = true
... | _ = false
abstract
  no-late-registry-candidate : filterᵇ (λ where (_ , s) → returnedRegistry s)
    (RegistryFind.reach 10 8 registryStart) ≡ []
  no-late-registry-candidate = refl

-- The witnessed endpoint is still closed/returned and has the new handler;
-- these are the existing checked increment-73 observations.
returned-after = Late.returned-after
closed-after = Late.closed-after
late-handler = Late.late-handler
late-not-collected = Late.late-not-collected

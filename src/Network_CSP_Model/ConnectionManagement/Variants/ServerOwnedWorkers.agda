{-# OPTIONS --guardedness #-}

-- Own every accepted admission Async and join its available result before CM
-- shutdown. No cancellation or worker/handler state write is added. Ordinary
-- transitions are the source transitions, followed by the boundary check.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Variants.ServerOwnedWorkers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; HandleId)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerPeers as Shared
import ConnectionManagement.ServerPeersRelays as Relays
import ConnectionManagement.Rules.PoolRelays as RR
module S = Server isBearerClosed
module E = Exit isBearerClosed
module K = Shared isBearerClosed isIOManagerError
private module SR = Relays isBearerClosed isIOManagerError

-- Historical handles are never removed. False means owned but not yet joined.
Ownership = Store WorkerId Bool

-- The finite registry is joined exactly when every retained handle is joined.
allJoined : Ownership → Bool
allJoined [] = true
allJoined ((_ , false) ∷ _) = false
allJoined ((_ , true) ∷ rest) = allJoined rest

-- Register only the successful accept handoff, atomically with its source edge.
track : K.Action → Ownership → Ownership
track (K.serverStep (E.run (S.acceptedFork w req))) owned = put w false owned
track _ owned = owned

-- Check every route entering or passing CM closure, including core aliases.
boundary : K.State → Ownership → Bool
boundary s owned with S.stage (E.base (K.server s))
... | S.closingCM = allJoined owned
... | S.serverReturned = allJoined owned
... | _ = true

-- A join observes an actual raw-worker result, and only writes the registry.
join : WorkerId → S.State → Ownership → Maybe Ownership
join w s owned with lookup w owned | S.resultOf w s
... | just false | just _ = just (put w true owned)
... | _ | _ = nothing

-- Shared-state variant, useful independently of the selected runtime.
record State : Set where
  constructor state
  field source : K.State
        owned : Ownership
open State public

-- The shared source step is reused without copying any source rule family.
step′ : K.Action → State → Maybe State
step′ a s with K.step a (source s)
... | nothing = nothing
... | just b with boundary b (track a (owned s))
...   | false = nothing
...   | true = just (state b (track a (owned s)))

-- Each successful shared edge retains exactly its source write.
step-erasure : ∀ a s {t} → step′ a s ≡ just t → K.step a (source s) ≡ just (source t)
step-erasure a s eq with K.step a (source s) in original
... | nothing = case eq of λ ()
... | just b with boundary b (track a (owned s))
...   | false = case eq of λ ()
...   | true = case just-injective eq of λ { refl → refl }

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  module T = K.Protocols canInitiate
  module SourceOuter = SR.Protocols canInitiate

  -- Runtime ownership lives next to, rather than inside, the existing runtime.
  record Runtime : Set where
    constructor runtime
    field source : T.Runtime
          owned : Ownership
  open Runtime public

  -- Only inherit and complete enact a shared source action; cover both.
  trackPlan : T.Plan → Ownership → Ownership
  trackPlan (T.inherit a _) owned = track a owned
  trackPlan (T.complete a _ _ _) owned = track a owned
  trackPlan _ owned = owned

  -- Keep the original plan write, including result caching and physical plans.
  enact′ : T.Plan → Runtime → Maybe Runtime
  enact′ p s with T.enact p (source s)
  ... | nothing = nothing
  ... | just b with boundary (T.base b) (trackPlan p (owned s))
  ...   | false = nothing
  ...   | true = just (runtime b (trackPlan p (owned s)))

  -- A successful guarded plan erases to that very source enactment.
  enact-erasure : ∀ p s {t} → enact′ p s ≡ just t → T.enact p (source s) ≡ just (source t)
  enact-erasure p s eq with T.enact p (source s) in original
  ... | nothing = case eq of λ ()
  ... | just b with boundary (T.base b) (trackPlan p (owned s))
  ...   | false = case eq of λ ()
  ...   | true = case just-injective eq of λ { refl → refl }

  -- Source events and the single additional join label are distinguished.
  data Event : Set where
    run : T.Event → Event
    joinWorker : WorkerId → Event

  -- Selection is unchanged; join cannot advance or terminate a source worker.
  advance′ : Event → Runtime → Maybe Runtime
  advance′ (run a) s with T.choose a (source s)
  ... | nothing = nothing
  ... | just p = enact′ p s
  advance′ (joinWorker w) s with join w (E.base (K.server (T.base (source s)))) (owned s)
  ... | nothing = nothing
  ... | just handles = just (runtime (source s) handles)

  -- Ordinary event erasure is one exact source event, with no extra premise.
  advance-erasure : ∀ a s {t} → advance′ (run a) s ≡ just t →
    T.advance a (source s) ≡ just (source t)
  advance-erasure a s eq with T.choose a (source s)
  ... | nothing = case eq of λ ()
  ... | just p = enact-erasure p s eq

  -- Exact effect of joining: source state unchanged and this handle marked true.
  join-effect : ∀ w s {t} → advance′ (joinWorker w) s ≡ just t →
    source t ≡ source s × owned t ≡ put w true (owned s)
  join-effect w s eq with lookup w (owned s) | S.resultOf w (E.base (K.server (T.base (source s))))
  ... | just false | just r = case just-injective eq of λ { refl → refl , refl }
  ... | just false | nothing = case eq of λ ()
  ... | just true | _ = case eq of λ ()
  ... | nothing | _ = case eq of λ ()

  -- Join is available precisely for an owned, unjoined worker with a result.
  join-ready : ∀ w s r → lookup w (owned s) ≡ just false →
    S.resultOf w (E.base (K.server (T.base (source s)))) ≡ just r →
    advance′ (joinWorker w) s ≡ just (runtime (source s) (put w true (owned s)))
  join-ready w s r found result rewrite found | result = refl

  -- The actual outer semantics freezes inner steps when relays cancellation starts.
  returned : Runtime → Bool
  returned s = SourceOuter.runtimeReturned (source s)
  open RR.Outer advance′ returned public

  -- Ownership erasure retains the original outer runtime and relays state.
  eraseOuter : Outer → SourceOuter.Outer
  eraseOuter (outer s r) = SourceOuter.outer (source s) r

  -- Join steps erase to the empty action list; all other labels are retained.
  eraseActions : List OuterAction → List SourceOuter.OuterAction
  eraseActions [] = []
  eraseActions (innerAct (run a) ∷ as) = SourceOuter.innerAct a ∷ eraseActions as
  eraseActions (innerAct (joinWorker w) ∷ as) = eraseActions as
  eraseActions (relaysAct a ∷ as) = SourceOuter.relaysAct a ∷ eraseActions as

  -- Ordinary inner edges lift unchanged through the outer scope.
  inner-erasure : ∀ a s {t} → outerStep (innerAct (run a)) s ≡ just t →
    SourceOuter.outerStep (SourceOuter.innerAct a) (eraseOuter s) ≡ just (eraseOuter t)
  inner-erasure a (outer s (RR.relaysState r RR.inside)) eq with advance′ (run a) s in stepped
  ... | nothing = case eq of λ ()
  ... | just b rewrite advance-erasure a s stepped = cong (λ x → just (eraseOuter x)) (just-injective eq)
  inner-erasure a (outer s (RR.relaysState r RR.cancelling)) eq = case eq of λ ()
  inner-erasure a (outer s (RR.relaysState r RR.finished)) eq = case eq of λ ()

  -- An outer join stutters on the entire source outer state, not just its CM.
  outer-join : ∀ w s {t} → outerStep (innerAct (joinWorker w)) s ≡ just t → eraseOuter t ≡ eraseOuter s
  outer-join w (outer s (RR.relaysState r RR.inside)) eq with advance′ (joinWorker w) s in stepped
  ... | nothing = case eq of λ ()
  ... | just b = subst (λ t → eraseOuter t ≡ eraseOuter (outer s (RR.relaysState r RR.inside)))
    (just-injective eq) (cong (λ x → SourceOuter.outer x (RR.relaysState r RR.inside)) (proj₁ (join-effect w s stepped)))
  outer-join w (outer s (RR.relaysState r RR.cancelling)) eq = case eq of λ ()
  outer-join w (outer s (RR.relaysState r RR.finished)) eq = case eq of λ ()

  -- Relays steps have the same return test and exactly the same physical write.
  relays-erasure : ∀ a s {t} → outerStep (relaysAct a) s ≡ just t →
    SourceOuter.outerStep (SourceOuter.relaysAct a) (eraseOuter s) ≡ just (eraseOuter t)
  relays-erasure a (outer s r) eq with RR.step (returned s) a r
  ... | nothing = case eq of λ ()
  ... | just r′ = cong (λ x → just (eraseOuter x)) (just-injective eq)

  -- Every variant run erases to a source run; joins are finite stuttering.
  outer-erasure : ∀ {s as t} → Executes s as t →
    SourceOuter.Executes (eraseOuter s) (eraseActions as) (eraseOuter t)
  outer-erasure done = SourceOuter.done
  outer-erasure (next {s = s} {a = innerAct (run a)} eq rest) = SourceOuter.next (inner-erasure a s eq) (outer-erasure rest)
  outer-erasure (next {s = s} {a = innerAct (joinWorker w)} eq rest) =
    subst (λ x → SourceOuter.Executes x _ _) (outer-join w s eq) (outer-erasure rest)
  outer-erasure (next {s = s} {a = relaysAct a} eq rest) = SourceOuter.next (relays-erasure a s eq) (outer-erasure rest)

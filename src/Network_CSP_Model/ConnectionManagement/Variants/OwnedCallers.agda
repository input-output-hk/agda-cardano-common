{-# OPTIONS --guardedness #-}

-- Owned-callers design variant, with the original selector and guarded enact.
-- Both inherit and complete use the guarded shared step; all other selected
-- plans retain source semantics. Thus no ServerPeers rule is copied. The outer
-- runtime uses the source outer types with a guarded inner transition. The
-- policy predicate on source runs is proved equivalent to guarded execution.
-- Raw peer core aliases are already refused by K.rawPeerAllowed; source Server
-- steps cannot begin CM calls (SourceKeysShared.server-keys). Selected direct
-- caller plans perform only a job runNext. The only extra restriction is the
-- two raw, foreign-only core begins, including under complete plans.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Variants.OwnedCallers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import ConnectionManagement.Domain using (HandleId)
open import ConnectionManagement.Store using (put)
open import Data.Nat using (ℕ)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Shared
import ConnectionManagement.ServerPeersRelays as Relays
import ConnectionManagement.Rules.PoolRelays as RR
module K = Shared isBearerClosed isIOManagerError
private module SR = Relays isBearerClosed isIOManagerError

-- Exactly raw CM call initialization is removed from shared actions.
ownedOnly : K.Action → Bool
ownedOnly (K.coreStep (O.beginAcquire _ _)) = false
ownedOnly (K.coreStep (O.beginRelease _ _)) = false
ownedOnly _ = true

-- The executable variant is the source shared step guarded by ownedOnly.
step′ : K.Action → K.State → Maybe K.State
step′ a s with ownedOnly a
... | false = nothing
... | true = K.step a s

-- A successful guarded step has exactly its original write and policy proof.
step-view : ∀ a s {t} → step′ a s ≡ just t → ownedOnly a ≡ true × K.step a s ≡ just t
step-view a s eq with ownedOnly a
... | false = case eq of λ ()
... | true = refl , eq

-- Policy plus an original step is sufficient for guarded execution.
step-build : ∀ a s {t} → ownedOnly a ≡ true → K.step a s ≡ just t → step′ a s ≡ just t
step-build a s ok eq with ownedOnly a
... | false = case ok of λ ()
... | true = eq

-- Shared executions use actual guarded transitions at every edge.
data Executes′ : K.State → List K.Action → K.State → Set where
  done′ : ∀ {s} → Executes′ s [] s
  next′ : ∀ {s t u a as} → step′ a s ≡ just t → Executes′ t as u → Executes′ s (a ∷ as) u

-- Restriction retains the source action list, states and actual transitions.
restriction : ∀ {s as t} → Executes′ s as t → K.Executes s as t
restriction done′ = K.done
restriction (next′ {s = s} {a = a} eq rest) = K.next (proj₂ (step-view a s eq)) (restriction rest)

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  module T = K.Protocols canInitiate
  module Outer = SR.Protocols canInitiate

  -- Every shared action enacted by either plan constructor must satisfy policy.
  planAllowed : T.Plan → Bool
  planAllowed (T.inherit a _) = ownedOnly a
  planAllowed (T.complete a _ _ _) = ownedOnly a
  planAllowed _ = true

  -- Selected plans retain their source writes, guarded before execution.
  enact′ : T.Plan → T.Runtime → Maybe T.Runtime
  enact′ p s with planAllowed p
  ... | false = nothing
  ... | true = T.enact p s

  -- A guarded plan is exactly a source plan satisfying its shared-action policy.
  enact-view : ∀ p s {t} → enact′ p s ≡ just t → planAllowed p ≡ true × T.enact p s ≡ just t
  enact-view p s eq with planAllowed p
  ... | false = case eq of λ ()
  ... | true = refl , eq

  -- Conversely an allowed source enact is a guarded enact.
  enact-build : ∀ p s {t} → planAllowed p ≡ true → T.enact p s ≡ just t → enact′ p s ≡ just t
  enact-build p s ok eq with planAllowed p
  ... | false = case ok of λ ()
  ... | true = eq

  -- Inherit executes exactly the guarded K step, without a rule copy.
  inherit-step : ∀ a f s {b} → step′ a (T.base s) ≡ just b →
    enact′ (T.inherit a f) s ≡ just (T.runtime b f)
  inherit-step a f s eq with step-view a (T.base s) eq
  ... | ok , original = enact-build (T.inherit a f) s ok (source original)
    where
    source : ∀ {b} → K.step a (T.base s) ≡ just b → T.enact (T.inherit a f) s ≡ just (T.runtime b f)
    source original with K.step a (T.base s)
    ... | nothing = case original of λ ()
    ... | just b = case just-injective original of λ { refl → refl }

  -- Runtime selection remains the original executable selection function.
  advance′ : T.Event → T.Runtime → Maybe T.Runtime
  advance′ a s with T.choose a s
  ... | nothing = nothing
  ... | just p = enact′ p s

  -- The run predicate inspects each actually selected plan's shared action.
  eventAllowed : T.Event → T.Runtime → Set
  eventAllowed a s with T.choose a s
  ... | nothing = ⊤
  ... | just p = planAllowed p ≡ true

  -- One guarded runtime edge is equivalent to an allowed original edge.
  advance-view : ∀ a s {t} → advance′ a s ≡ just t → eventAllowed a s × T.advance a s ≡ just t
  advance-view a s eq with T.choose a s
  ... | nothing = case eq of λ ()
  ... | just p = enact-view p s eq

  -- This reverse implication establishes equality of allowed run notions.
  advance-build : ∀ a s {t} → eventAllowed a s → T.advance a s ≡ just t → advance′ a s ≡ just t
  advance-build a s ok eq with T.choose a s
  ... | nothing = case eq of λ ()
  ... | just p = enact-build p s ok eq

  -- Guarded runtime executions use the unchanged source runtime and labels.
  data Runs′ : T.Runtime → List T.Event → T.Runtime → Set where
    stop′ : ∀ {s} → Runs′ s [] s
    more′ : ∀ {s t u a as} → advance′ a s ≡ just t → Runs′ t as u → Runs′ s (a ∷ as) u

  -- Every variant runtime run is a source-model runtime run.
  runs-restriction : ∀ {s as t} → Runs′ s as t → T.Runs s as t
  runs-restriction stop′ = T.stop
  runs-restriction (more′ {s = s} {a = a} eq rest) = T.more (proj₂ (advance-view a s eq)) (runs-restriction rest)

  -- The outer step retains the source relays semantics and guards inner steps.
  outerStep′ : Outer.OuterAction → Outer.Outer → Maybe Outer.Outer
  outerStep′ (Outer.innerAct a) (Outer.outer s (RR.relaysState t RR.inside)) with advance′ a s
  ... | nothing = nothing
  ... | just s′ = just (Outer.outer s′ (RR.relaysState t RR.inside))
  outerStep′ (Outer.innerAct a) (Outer.outer s (RR.relaysState t RR.cancelling)) = nothing
  outerStep′ (Outer.innerAct a) (Outer.outer s (RR.relaysState t RR.finished)) = nothing
  outerStep′ (Outer.relaysAct a) s = Outer.outerStep (Outer.relaysAct a) s

  -- Outer policy is trivial on relays and checks selected plans on inner edges.
  outerAllowed : Outer.OuterAction → Outer.Outer → Set
  outerAllowed (Outer.innerAct a) s = eventAllowed a (Outer.inner s)
  outerAllowed (Outer.relaysAct a) s = ⊤

  -- This is the pointwise equivalence of guarded and policy-filtered outer steps.
  outer-view : ∀ a s {t} → outerStep′ a s ≡ just t → outerAllowed a s × Outer.outerStep a s ≡ just t
  outer-view (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.inside)) eq with advance′ a s in stepped
  ... | nothing = case eq of λ ()
  ... | just s′ with advance-view a s stepped
  ...   | ok , original rewrite original = ok , eq
  outer-view (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.cancelling)) eq = case eq of λ ()
  outer-view (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.finished)) eq = case eq of λ ()
  outer-view (Outer.relaysAct a) s eq = tt , eq

  -- Allowed source outer steps run under the guarded semantics as well.
  outer-build : ∀ a s {t} → outerAllowed a s → Outer.outerStep a s ≡ just t → outerStep′ a s ≡ just t
  outer-build (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.inside)) ok eq with T.advance a s in stepped
  ... | nothing = case eq of λ ()
  ... | just s′ rewrite advance-build a s ok stepped = eq
  outer-build (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.cancelling)) ok eq = case eq of λ ()
  outer-build (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.finished)) ok eq = case eq of λ ()
  outer-build (Outer.relaysAct a) s ok eq = eq

  -- Executable outer runs end in the same source outer states.
  data OuterRuns′ : Outer.Outer → List Outer.OuterAction → Outer.Outer → Set where
    outer-done′ : ∀ {s} → OuterRuns′ s [] s
    outer-next′ : ∀ {s t u a as} → outerStep′ a s ≡ just t → OuterRuns′ t as u → OuterRuns′ s (a ∷ as) u

  -- Source restriction applies SI5 and every other source outer-run theorem.
  outer-restriction : ∀ {s as t} → OuterRuns′ s as t → Outer.Executes s as t
  outer-restriction outer-done′ = Outer.done
  outer-restriction (outer-next′ {s = s} {a = a} eq rest) = Outer.next (proj₂ (outer-view a s eq)) (outer-restriction rest)

  -- Equivalent predicate presentation on the actual source execution proof.
  Allowed : ∀ {s as t} → Outer.Executes s as t → Set
  Allowed Outer.done = ⊤
  Allowed (Outer.next {s = s} {a = a} eq rest) = outerAllowed a s × Allowed rest

  -- Every source run with allowed enacted plans is an executable variant run.
  allowed-build : ∀ {s as t} (path : Outer.Executes s as t) → Allowed path → OuterRuns′ s as t
  allowed-build Outer.done ok = outer-done′
  allowed-build (Outer.next {s = s} {a = a} eq rest) (ok , later) =
    outer-next′ (outer-build a s ok eq) (allowed-build rest later)

  -- Every executable variant run carries the policy predicate on its restriction.
  allowed-view : ∀ {s as t} (path : OuterRuns′ s as t) → Allowed (outer-restriction path)
  allowed-view outer-done′ = tt
  allowed-view (outer-next′ {s = s} {a = a} eq rest) = proj₁ (outer-view a s eq) , allowed-view rest

  -- This event-only policy is equivalent on successful selected plans: every
  -- non-dispatch frontend constructor selects owned steps or metadata writes.
  -- The converse direction is certified by OwnedCallersSelection.choose-shape.
  eventOnly : T.Event → Bool
  eventOnly (T.dispatch a) = ownedOnly a
  eventOnly _ = true

  -- A successful guarded dispatch exposes its ownedOnly conjunct.
  advance-event-policy : ∀ a s {t} → advance′ a s ≡ just t → eventOnly a ≡ true
  advance-event-policy (T.dispatch a) s eq with T.inheritAllowed a s
  ... | false = case eq of λ ()
  ... | true = proj₁ (enact-view (T.inherit a (T.noteLegacy a (T.front s))) s eq)
  advance-event-policy (T.startNext j rid) s eq = refl
  advance-event-policy (T.selectStart w) s eq = refl
  advance-event-policy (T.invokeStartTrace w) s eq = refl
  advance-event-policy (T.returnStartTrace w) s eq = refl
  advance-event-policy (T.forkStart w j) s eq = refl
  advance-event-policy (T.registerStart j) s eq = refl
  advance-event-policy (T.commitClean j) s eq = refl
  advance-event-policy (T.commitError j err) s eq = refl
  advance-event-policy (T.pollResults ref w) s eq = refl
  advance-event-policy (T.waitJobResults j) s eq = refl
  advance-event-policy (T.waitMonitorResults ref) s eq = refl
  advance-event-policy (T.observeStartTraceException w result) s eq = refl
  advance-event-policy (T.deliverStartTraceShutdown err) s eq = refl

  -- A complete plan runs the same guarded K step before the unchanged cache write.
  complete-step : ∀ a rid r result s {b} → step′ a (T.base s) ≡ just b →
    enact′ (T.complete a rid r result) s ≡ just (T.runtime (T.cacheResult rid r result (T.front s) b)
      (record (T.front s) { calls = put rid (record r { value = just result }) (T.calls (T.front s)) }))
  complete-step a rid r result s eq with step-view a (T.base s) eq
  ... | ok , original = enact-build (T.complete a rid r result) s ok (source original)
    where
    source : ∀ {b} → K.step a (T.base s) ≡ just b →
      T.enact (T.complete a rid r result) s ≡ just (T.runtime (T.cacheResult rid r result (T.front s) b)
        (record (T.front s) { calls = put rid (record r { value = just result }) (T.calls (T.front s)) }))
    source original with K.step a (T.base s)
    ... | nothing = case original of λ ()
    ... | just b = case just-injective original of λ { refl → refl }

  -- Conversely every guarded inherit enact contains an actual guarded shared step.
  inherit-view : ∀ a f s {t} → enact′ (T.inherit a f) s ≡ just t →
    Σ K.State (λ b → step′ a (T.base s) ≡ just b × t ≡ T.runtime b f)
  inherit-view a f s eq with enact-view (T.inherit a f) s eq
  ... | ok , original with K.step a (T.base s) in stepped
  ...   | nothing = case original of λ ()
  ...   | just b = b , step-build a (T.base s) ok stepped , sym (just-injective original)

  -- The same reverse correspondence covers the other shared-step plan wrapper.
  complete-view : ∀ a rid r result s {t} → enact′ (T.complete a rid r result) s ≡ just t →
    Σ K.State (λ b → step′ a (T.base s) ≡ just b ×
      t ≡ T.runtime (T.cacheResult rid r result (T.front s) b)
        (record (T.front s) { calls = put rid (record r { value = just result }) (T.calls (T.front s)) }))
  complete-view a rid r result s eq with enact-view (T.complete a rid r result) s eq
  ... | ok , original with K.step a (T.base s) in stepped
  ...   | nothing = case original of λ ()
  ...   | just b = b , step-build a (T.base s) ok stepped , sym (just-injective original)

{-# OPTIONS --guardedness #-}

-- Full raw alphabet of the supervised frontend and its outer relays scope.
-- Both renderers delegate to the existing machine; no rules are replicated.
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import ConnectionManagement.Domain using (ErrorId; HandleId)
module ConnectionManagement.CSP.Supervised
  (isBearerClosed isIOManagerError : ErrorId → Bool)
  (canInitiate : HandleId → ℕ → Bool) where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
import Relation.Nullary
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.ServerPeersRelays as Relays
import ConnectionManagement.Rules.PoolRelays as Pool
import ConnectionManagement.CSP.Dispatcher as Render
module O = Relays.Protocols isBearerClosed isIOManagerError canInitiate
module T = O.V
module Raw = Render O.Outer O.OuterAction O.outerStep
open Raw public hiding (Executes; done; next; exec-intro; exec-inv;
  trace-intro; trace-inv; all-exec-inv; reject-execution; refused-extension)
open import Process_Trees using (ExtI)
open import Semantics.Failures {E = Channel} {I = ExtI Channel}
  using (_⟹⟨_⟩_; traces)

-- Structural conversion preserves every actual outer edge and endpoint.
to-raw : ∀ {s as t} → O.Executes s as t → Raw.Executes s as t
to-raw O.done = Raw.done
to-raw (O.next eq rest) = Raw.next eq (to-raw rest)
from-raw : ∀ {s as t} → Raw.Executes s as t → O.Executes s as t
from-raw Raw.done = O.done
from-raw (Raw.next eq rest) = O.next eq (from-raw rest)

exec-intro : ∀ {s as t} → O.Executes s as t →
  Process s ⟹⟨ map label as ⟩ Process t
exec-intro run = Raw.exec-intro (to-raw run)
exec-inv : ∀ {s as P} → Process s ⟹⟨ map label as ⟩ P →
  Σ O.Outer (λ t → P ≡ Process t × O.Executes s as t)
exec-inv tr with Raw.exec-inv tr
... | t , eq , run = t , eq , from-raw run
trace-intro : ∀ {s as t} → O.Executes s as t → traces (Process s) (map label as)
trace-intro run = Raw.trace-intro (to-raw run)
trace-inv : ∀ {s as} → traces (Process s) (map label as) →
  Σ O.Outer (λ t → O.Executes s as t)
trace-inv tr with Raw.trace-inv tr
... | t , run = t , from-raw run
all-exec-inv : ∀ {s es P} → Process s ⟹⟨ es ⟩ P →
  Σ (List O.OuterAction) (λ as → Σ O.Outer (λ t →
    es ≡ map label as × P ≡ Process t × O.Executes s as t))
all-exec-inv tr with Raw.all-exec-inv tr
... | as , t , eq , endpoint , run = as , t , eq , endpoint , from-raw run
refused-extension : ∀ {s as t a} → O.Executes s as t → O.outerStep a t ≡ nothing →
  Relation.Nullary.¬ traces (Process s) (map label (as Data.List.++ (a ∷ [])))
refused-extension run disabled = Raw.refused-extension (to-raw run) disabled

-- Inner histories embed while the relays owner remains inside. Relays actions
-- themselves are covered directly above, including cancel/deliver/join/finish.
lift-edge : ∀ {s t a} r → T.advance a s ≡ just t →
  O.outerStep (O.innerAct a) (O.outer s (Pool.relaysState r Pool.inside)) ≡
    just (O.outer t (Pool.relaysState r Pool.inside))
lift-edge r eq rewrite eq = refl
lift-run : ∀ {s as t} r → T.Runs s as t →
  O.Executes (O.outer s (Pool.relaysState r Pool.inside))
    (map O.innerAct as) (O.outer t (Pool.relaysState r Pool.inside))
lift-run r T.stop = O.done
lift-run r (T.more {s = s} {t = t} {a = a} eq rest) =
  O.next (lift-edge {s = s} {t = t} {a = a} r eq) (lift-run r rest)


-- Every arbitrary raw trace (not only pre-encoded action lists) is recovered.
all-trace-inv : ∀ {s es} → traces (Process s) es →
  Σ (List O.OuterAction) (λ as → Σ O.Outer (λ t →
    es ≡ map label as × O.Executes s as t))
all-trace-inv (_ , tr) with all-exec-inv tr
... | as , t , eq , endpoint , run = as , t , eq , run

open import Data.Unit using (⊤)
open import Semantics.LTS {E = Channel} {I = ExtI Channel} using (Event√)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (failures)

-- Stable failures retain native histories and exact machine endpoints.
native-failure-intro : ∀ {ℓ} {s as t} {X : Event√ ⊤ → Set ℓ} →
  O.Executes s as t → DisabledSet t X → failures (Process s) (map label as) X
native-failure-intro run disabled = Raw.failure-intro (to-raw run) disabled
native-failure-inv : ∀ {ℓ} {s as} {X : Event√ ⊤ → Set ℓ} →
  failures (Process s) (map label as) X →
  Σ O.Outer (λ t → O.Executes s as t × DisabledSet t X)
native-failure-inv failure with Raw.failure-inv failure
... | t , run , disabled = t , from-raw run , disabled

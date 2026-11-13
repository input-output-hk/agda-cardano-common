{-# OPTIONS --guardedness #-}

-- Full raw alphabet of the supervised frontend and its outer relays scope.
-- Both renderers delegate to the existing machine; no rules are replicated.
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import ConnectionManagement.Domain using (ErrorId; HandleId)
module ConnectionManagement.CSP.SupervisedInner
  (isBearerClosed isIOManagerError : ErrorId → Bool)
  (canInitiate : HandleId → ℕ → Bool) where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
import Relation.Nullary
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.ServerPeersRelays as Relays
import ConnectionManagement.CSP.Dispatcher as Render
module O = Relays.Protocols isBearerClosed isIOManagerError canInitiate
module T = O.V
open import Process_Trees using (ExtI)
module Raw = Render T.Runtime T.Event T.advance
open Raw public hiding (Executes; done; next; exec-intro; exec-inv;
  trace-intro; trace-inv; all-exec-inv; reject-execution; refused-extension)
open import Semantics.Failures {E = Channel} {I = ExtI Channel}
  using (_⟹⟨_⟩_; traces)
to-raw : ∀ {s as t} → T.Runs s as t → Raw.Executes s as t
to-raw T.stop = Raw.done
to-raw (T.more eq rest) = Raw.next eq (to-raw rest)
from-raw : ∀ {s as t} → Raw.Executes s as t → T.Runs s as t
from-raw Raw.done = T.stop
from-raw (Raw.next eq rest) = T.more eq (from-raw rest)
exec-intro : ∀ {s as t} → T.Runs s as t → Process s ⟹⟨ map label as ⟩ Process t
exec-intro run = Raw.exec-intro (to-raw run)
exec-inv : ∀ {s as P} → Process s ⟹⟨ map label as ⟩ P →
  Σ T.Runtime (λ t → P ≡ Process t × T.Runs s as t)
exec-inv tr with Raw.exec-inv tr
... | t , eq , run = t , eq , from-raw run
trace-intro : ∀ {s as t} → T.Runs s as t → traces (Process s) (map label as)
trace-intro run = Raw.trace-intro (to-raw run)
trace-inv : ∀ {s as} → traces (Process s) (map label as) →
  Σ T.Runtime (λ t → T.Runs s as t)
trace-inv tr with Raw.trace-inv tr
... | t , run = t , from-raw run

-- The arbitrary-trace inverse also excludes extra tau/tick behavior inside.
all-trace-inv : ∀ {s es} → traces (Process s) es →
  Σ (List T.Event) (λ as → Σ T.Runtime (λ t →
    es ≡ map label as × T.Runs s as t))
all-trace-inv (_ , tr) with Raw.all-exec-inv tr
... | as , t , eq , endpoint , run = as , t , eq , from-raw run

open import Data.Unit using (⊤)
open import Semantics.LTS {E = Channel} {I = ExtI Channel} using (Event√)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (failures)

-- Stable failures retain native histories and exact machine endpoints.
native-failure-intro : ∀ {ℓ} {s as t} {X : Event√ ⊤ → Set ℓ} →
  T.Runs s as t → DisabledSet t X → failures (Process s) (map label as) X
native-failure-intro run disabled = Raw.failure-intro (to-raw run) disabled
native-failure-inv : ∀ {ℓ} {s as} {X : Event√ ⊤ → Set ℓ} →
  failures (Process s) (map label as) X →
  Σ T.Runtime (λ t → T.Runs s as t × DisabledSet t X)
native-failure-inv failure with Raw.failure-inv failure
... | t , run , disabled = t , from-raw run , disabled

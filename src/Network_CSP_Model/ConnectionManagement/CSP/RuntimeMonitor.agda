{-# OPTIONS --guardedness #-}

-- Replay diagnostics for the entire supplied event type, not a legacy action
-- classifier. A refusal is left unclassified; it is not a deadlock certificate.
open import Data.Maybe using (Maybe)
module ConnectionManagement.CSP.RuntimeMonitor
  (State Action : Set) (advance : Action → State → Maybe State) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.CSP.Dispatcher as Dispatcher
module Raw = Dispatcher State Action advance

-- Unsupported/malformed are explicit input-adapter reports, never inferred
-- from a disabled action. Codes identify the missing feature or parse error.
data Request : Set where
  event : Action → Request
  malformed unsupported : ℕ → Request

-- These are frontiers in replay, not extra transitions of the rendered process.
-- A cutoff retains the unconsumed suffix; empty input completes even at fuel 0.
data Report : State → List Request → Set where
  complete : ∀ {s} → Report s []
  cutoff : ∀ {s r rs} → Report s (r ∷ rs)
  malformed-input : ∀ {s code rs} → Report s (malformed code ∷ rs)
  model-frontier : ∀ {s code rs} → Report s (unsupported code ∷ rs)
  refused : ∀ {s a rs} → advance a s ≡ nothing → Report s (event a ∷ rs)
  advanced : ∀ {s a t rs} → advance a s ≡ just t → Report t rs →
    Report s (event a ∷ rs)

-- Parsing/model gaps take priority over fuel; no enabledness search is implied.
replay : (fuel : ℕ) (s : State) (rs : List Request) → Report s rs

-- Name the dispatcher result explicitly, keeping its equality available without
-- abstracting a dependent run proof during the acceptance induction.
branch : (fuel : ℕ) (s : State) (a : Action) (rs : List Request)
  (result : Maybe State) → advance a s ≡ result → Report s (event a ∷ rs)
branch n s a rs nothing eq = refused eq
branch n s a rs (just t) eq = advanced eq (replay n t rs)

replay n s [] = complete
replay n s (malformed code ∷ rs) = malformed-input
replay n s (unsupported code ∷ rs) = model-frontier
replay zero s (event a ∷ rs) = cutoff
replay (suc n) s (event a ∷ rs) = branch n s a rs (advance a s) refl

-- Only a fully consumed, successfully executed request list is accepted.
Accepted : ∀ {s rs} → Report s rs → Set
Accepted complete = ⊤
Accepted (advanced eq tail) = Accepted tail
Accepted _ = ⊥
actions : List Request → List Action
actions [] = []
actions (event a ∷ rs) = a ∷ actions rs
actions (_ ∷ rs) = actions rs

accepted-run : ∀ {s rs} (report : Report s rs) → Accepted report →
  Σ State (λ t → Raw.Executes s (actions rs) t)
accepted-run complete tt = _ , Raw.done
accepted-run (advanced eq tail) ok with accepted-run tail ok
... | t , path = t , Raw.next eq path
accepted-run cutoff ()
accepted-run malformed-input ()
accepted-run model-frontier ()
accepted-run (refused eq) ()

-- Existing checked histories are accepted without normalizing their schedules.
-- Fuel counts dispatched events, not allocation or state-space exploration.
open import Data.List using (map; length)
accepted-branch : ∀ n s a rs result (found : advance a s ≡ result) {t} →
  result ≡ just t → Accepted (replay n t rs) →
  Accepted (branch n s a rs result found)
accepted-branch n s a rs (just t) found refl ok = ok

replay-run : ∀ {s as t} → Raw.Executes s as t →
  Accepted (replay (length as) s (map event as))
replay-run Raw.done = tt
replay-run (Raw.next {s = s} {a = a} {as = as} eq rest) =
  accepted-branch (length as) s a (map event as) (advance a s) refl eq (replay-run rest)

-- Optional domain-specific explanations must supply evidence. In particular,
-- an unclassified refusal cannot silently become ordinary STM/transport wait
-- or an incomplete-model frontier. No completeness premise is manufactured.
module Explain (Blocking Missing : State → Action → Set) where
  data Cause (s : State) (a : Action) : Set where
    ordinary-blocking : Blocking s a → Cause s a
    incomplete-model : Missing s a → Cause s a
    unclassified : Cause s a
  record Refusal (s : State) (a : Action) : Set where
    constructor explanation
    field disabled : advance a s ≡ nothing
          cause : Cause s a

open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (cong)
open import Process_Trees using (ExtI)
open import Semantics.LTS {E = Raw.Channel} {I = ExtI Raw.Channel}
  using (Event; Event√; evl; √)
open import Semantics.Refusals {E = Raw.Channel} {I = ExtI Raw.Channel} using (Refuses)

-- Verified adapter for the full typed rendering alphabet. Tick is not a machine
-- action; the visible alphabet never produces malformed/unsupported requests.
-- This makes no claim about parsing external bytes or a Haskell log format.
decode-input : Event√ ⊤ → Request
decode-input (evl e) = event (Raw.decode-event e)
decode-input (√ _) = malformed 0
decode-input-label : ∀ a → decode-input (Raw.label a) ≡ event a
decode-input-label a = refl
visible-input-covered : ∀ e → Σ Action (λ a → decode-input (evl e) ≡ event a)
visible-input-covered e = Raw.decode-event e , refl
input-unique : ∀ {a b} → Raw.label a ≡ Raw.label b → event a ≡ event b
input-unique eq = cong event (Raw.label-injective eq)

-- Every disabled replay edge has a stable-refusal explanation and conversely.
-- This is an exact machine explanation, independent of optional wait/gap causes.
refusal-rendering : ∀ {s a} → advance a s ≡ nothing →
  Refuses (Raw.Process s) (λ e → e ≡ Raw.label a)
refusal-rendering = Raw.singleton-refusal
rendering-refusal : ∀ {s a} → Refuses (Raw.Process s) (λ e → e ≡ Raw.label a) →
  advance a s ≡ nothing
rendering-refusal = Raw.singleton-refusal-inv

-- Monitor the encoded schedule using the verified adapter, with no declarations
-- of unsupported coverage. Acceptance follows from the actual machine history.
open import Relation.Binary.PropositionalEquality using (refl)
decode-schedule : ∀ as → map decode-input (map Raw.label as) ≡ map event as
decode-schedule [] = refl
decode-schedule (a ∷ as) rewrite decode-schedule as = refl
replay-rendered-run : ∀ {s as t} → Raw.Executes s as t →
  Accepted (replay (length as) s (map decode-input (map Raw.label as)))
replay-rendered-run {as = as} run rewrite decode-schedule as = replay-run run

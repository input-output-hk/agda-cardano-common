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

{-# OPTIONS --safe #-}

-- One-step progress plus the checked work bound yields finite target reachability.
module Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress
  (Notification Return : Set) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_≤_; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Induction.WellFounded using (Acc; acc)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification Return as Cost
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingRank Notification Return as Rank
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Work

-- Targets can distinguish local server completion from full clean paired completion.
data Clean : D.State → Set where
  clean : ∀ {a x} → Clean (D.pair (C.client C.closed C.idle [] [] 0 a true (just x))
    (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing)

-- Every productive operation is an actual hidden step or exact visible wire record.
data Move (contract : S.Contract) : D.State → D.State → Set where
  internal : ∀ {s t} → D.Tau contract s t → Move contract s t
  wire : ∀ {s row t} → D.Step contract s row t → Move contract s t

-- A fully closed pair has no protocol operation left; it may still receive external input records.
clean-terminal : ∀ {p s t} → Clean s → Move p s t → ⊥
clean-terminal clean (wire ())
clean-terminal clean (internal (D.clientInternal ()))
clean-terminal clean (internal (D.serverInternal ()))
clean-terminal clean (internal (D.clientCallback _ ()))
clean-terminal clean (internal (D.serverCallback ()))
clean-terminal clean (internal (D.commitClient ()))
clean-terminal clean (internal (D.commitServer {m = D.reply _} ()))
clean-terminal clean (internal (D.commitServer {m = D.done} ()))

-- The proven potential decreases for either kind of productive shutdown move.
decreases : ∀ {p s t} → Move p s t → Work.BothStopping s → Cost.rank t < Cost.rank s
decreases (internal pr) _ = Rank.decreases pr
decreases (wire pr) both = Work.visible-decreases pr both

-- Both shutdown control predicates persist across either kind of productive move.
stays : ∀ {p s t} → Move p s t → Work.BothStopping s → Work.BothStopping t
stays (internal pr) = Work.tau-stays pr
stays (wire pr) = Work.step-stays pr

-- Exactly the observed wire row is retained; hidden operations contribute no row.
rows : ∀ {p s t} → Move p s t → List D.Event
rows (internal _) = []
rows (wire {row = row} _) = row ∷ []

-- A supplied operation prefixes its actual independent driver execution.
prepend : ∀ {p s t events u} (move : Move p s t) → D.Run p t events u → D.Run p s (rows move ++ events) u
prepend (internal pr) run = D.internal pr run
prepend (wire pr) run = D.visible pr run

-- These are local progress obligations, not an assumption of eventual target reachability.
record LocalProgress (contract : S.Contract) (Target Invariant : D.State → Set) : Set where
  field
    preserve : ∀ {s t} → Move contract s t → Invariant s → Invariant t
    ready : ∀ {s} → Invariant s → Work.BothStopping s →
      Target s ⊎ (¬ Target s × Σ[ t ∈ D.State ] Move contract s t)
open LocalProgress public

-- A completed path exposes its real source trace, target evidence and operation bound.
record Completion (contract : S.Contract) (Target : D.State → Set) (s : D.State) : Set where
  constructor completion
  field
    events : List D.Event
    target : D.State
    execution : D.Run contract s events target
    reached : Target target
    bounded : Work.steps execution ≤ Cost.rank s
open Completion public

-- Completion follows constructively once the stated invariant/local-progress contract is supplied.
module With (contract : S.Contract) (Target Invariant : D.State → Set)
  (progress : LocalProgress contract Target Invariant) where

  -- Every actual source continuation preserves the caller's structural invariant.
  run-preserve : ∀ {s events t} → D.Run contract s events t → Invariant s → Invariant t
  run-preserve D.stop invariant = invariant
  run-preserve (D.internal pr run) invariant = run-preserve run (preserve progress (internal pr) invariant)
  run-preserve (D.visible pr run) invariant = run-preserve run (preserve progress (wire pr) invariant)

  -- The paired shutdown region is preserved without an extra fairness assumption.
  run-stays : ∀ {s events t} → D.Run contract s events t → Work.BothStopping s → Work.BothStopping t
  run-stays D.stop both = both
  run-stays (D.internal pr run) both = run-stays run (Work.tau-stays pr both)
  run-stays (D.visible pr run) both = run-stays run (Work.step-stays pr both)

  -- Induction consumes actual potential, rather than placing termination in a new axiom.
  from-rank : ∀ s → Invariant s → Work.BothStopping s → Acc _<_ (Cost.rank s) → Completion contract Target s
  from-rank s invariant both (acc smaller) with ready progress invariant both
  ... | inj₁ reached = completion [] s D.stop reached (Work.bounded {p = contract} {s = s} D.stop both)
  ... | inj₂ (unfinished , t , next)
    with from-rank t (preserve progress next invariant) (stays next both) (smaller (decreases next both))
  ...   | completion events u run reached bounded =
    completion (rows next ++ events) u (prepend next run) reached (Work.bounded (prepend next run) both)

  -- This is model-level existence; an implementation still needs operation responsiveness.
  complete : ∀ {s} → Invariant s → Work.BothStopping s → Completion contract Target s
  complete {s} invariant both = from-rank s invariant both (<-wellFounded (Cost.rank s))

  -- Any finite maximal successful model execution ends at the target under local progress.
  maximal-completes : ∀ {s events t} → D.Run contract s events t → Invariant s → Work.BothStopping s →
    (∀ {u} → Move contract t u → ⊥) → Target t
  maximal-completes run invariant both maximal with ready progress (run-preserve run invariant) (run-stays run both)
  ... | inj₁ reached = reached
  ... | inj₂ (unfinished , u , next) = ⊥-elim (maximal next)

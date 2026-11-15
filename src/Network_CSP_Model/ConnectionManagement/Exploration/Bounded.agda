{-# OPTIONS --guardedness #-}

-- Exhaustive branching over a declared finite alphabet. The dispatcher remains
-- the sole enabledness test; the allocation guard never disguises a refusal.
open import Data.Maybe using (Maybe)
open import Data.List using (List)
open import Data.Nat using (ℕ)
module ConnectionManagement.Exploration.Bounded
  (State Action : Set) (advance : Action → State → Maybe State)
  (alphabet : List Action) (allocated : State → ℕ) where

open import Data.List using (List; []; _∷_; map; concatMap; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≤?_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)
open import ConnectionManagement.Exploration.Finite
import ConnectionManagement.CSP.Dispatcher as Dispatcher
module Raw = Dispatcher State Action advance

-- Retain successors so reachability never re-dispatches a listed enabled edge.
enabledFrom : List Action → State → List (Action × State)
enabledFrom [] s = []
enabledFrom (a ∷ as) s with advance a s
... | nothing = enabledFrom as s
... | just t = (a , t) ∷ enabledFrom as s
enabled : State → List (Action × State)
enabled = enabledFrom alphabet

soundFrom : ∀ xs s {a t} → (a , t) ∈ enabledFrom xs s →
  a ∈ xs × advance a s ≡ just t
soundFrom (a ∷ as) s p with advance a s in eq
... | nothing with soundFrom as s p
...   | member , edge = there member , edge
soundFrom (a ∷ as) s here | just t = here , eq
soundFrom (a ∷ as) s (there p) | just t with soundFrom as s p
... | member , edge = there member , edge

completeFrom : ∀ xs s {a t} → a ∈ xs → advance a s ≡ just t →
  (a , t) ∈ enabledFrom xs s
completeFrom (a ∷ as) s here edge with advance a s in eq
... | nothing with edge
...   | ()
completeFrom (a ∷ as) s here edge | just t with just-injective edge
... | refl = here
completeFrom (a ∷ as) s (there member) edge with advance a s
... | nothing = completeFrom as s member edge
... | just t = there (completeFrom as s member edge)

enabled-sound : ∀ {s a t} → (a , t) ∈ enabled s → a ∈ alphabet × advance a s ≡ just t
enabled-sound {s} = soundFrom alphabet s
enabled-complete : ∀ {s a t} → a ∈ alphabet → advance a s ≡ just t → (a , t) ∈ enabled s
enabled-complete {s} = completeFrom alphabet s

-- Empty traces are included; at depth zero their endpoint is still checked.
prepend : Action → List Action × State → List Action × State
prepend a (as , t) = (a ∷ as) , t
reach : ℕ → ℕ → State → List (List Action × State)
reach n budget s with allocated s ≤? budget
... | no _ = []
reach zero budget s | yes _ = ([] , s) ∷ []
reach (suc n) budget s | yes _ = ([] , s) ∷
  concatMap (λ where (a , t) → map (prepend a) (reach n budget t)) (enabled s)

-- Bounds constrain every visited state, including the initializer and endpoint.
data BoundedRun (budget : ℕ) : State → List Action → State → Set where
  stop : ∀ {s} → allocated s ≤ budget → BoundedRun budget s [] s
  more : ∀ {s t u a as} → allocated s ≤ budget → a ∈ alphabet →
    advance a s ≡ just t → BoundedRun budget t as u → BoundedRun budget s (a ∷ as) u
real-run : ∀ {b s as t} → BoundedRun b s as t → Raw.Executes s as t
real-run (stop _) = Raw.done
real-run (more _ _ eq rest) = Raw.next eq (real-run rest)

reach-sound : ∀ n b s {as t} → (as , t) ∈ reach n b s →
  length as ≤ n × BoundedRun b s as t
reach-sound n b s p with allocated s ≤? b
... | no _ with p
...   | ()
reach-sound zero b s here | yes within = z≤n , stop within
reach-sound (suc n) b s here | yes within = z≤n , stop within
reach-sound (suc n) b s (there p) | yes within
  with bind-out {A = Action × State} (λ where (a , t) → map (prepend a) (reach n b t)) {xs = enabled s} p
... | (a , mid) , member , tail with map-out (prepend a) tail
... | (as , t) , found , refl with enabled-sound member | reach-sound n b mid found
... | covered , eq | depth , path = s≤s depth , more within covered eq path

reach-complete : ∀ n {b s as t} → BoundedRun b s as t → length as ≤ n →
  (as , t) ∈ reach n b s
reach-complete n {b} {s} run depth with allocated s ≤? b
... | no outside with run
...   | stop within = ⊥-elim (outside within)
...   | more within _ _ _ = ⊥-elim (outside within)
reach-complete zero (stop _) depth | yes _ = here
reach-complete (suc n) (stop _) depth | yes _ = here
reach-complete (suc n) (more _ member eq rest) (s≤s depth) | yes _ =
  there (bind-in {A = Action × State} (λ where (a , t) → map (prepend a) (reach n _ t))
    (enabled-complete member eq) (map-in (prepend _) (reach-complete n rest depth)))

-- An executable, sufficient allocation cutoff for a supplied finite schedule.
-- It computes the maximum observed allocation, stopping at the first refusal.
budgetFor : State → List Action → ℕ
budgetFor s [] = allocated s
budgetFor s (a ∷ as) with advance a s
... | nothing = allocated s
... | just t = allocated s ⊔ budgetFor t as

-- This induction uses the run certificate, avoiding normalization of a search.
run-with-budget : ∀ {s as t} → (run : Raw.Executes s as t) → Covered as alphabet →
  ∀ b → budgetFor s as ≤ b → BoundedRun b s as t
run-with-budget Raw.done covered b within = stop within
run-with-budget {s} {a ∷ as} (Raw.next {t = mid} eq rest) (member , covered) b within
  with advance a s in found
... | nothing with eq
...   | ()
run-with-budget {s} {a ∷ as} (Raw.next {t = mid} eq rest) (member , covered) b within | just t with just-injective eq
...   | refl = more (≤-trans (m≤m⊔n (allocated s) (budgetFor t as)) within) member found
    (run-with-budget rest covered b (≤-trans (m≤n⊔m (allocated s) (budgetFor t as)) within))

witness-membership : ∀ {s as t} → Raw.Executes s as t → Covered as alphabet →
  (as , t) ∈ reach (length as) (budgetFor s as) s
witness-membership run covered = reach-complete _ (run-with-budget run covered _ ≤-refl) ≤-refl

-- Frontiers are search reports, never machine transitions or deadlock claims.
data Frontier : Set where
  allocation-cutoff depth-cutoff exhausted branching : Frontier
frontier : ℕ → ℕ → State → Frontier
frontier n b s with allocated s ≤? b
... | no _ = allocation-cutoff
frontier zero b s | yes _ = depth-cutoff
frontier (suc n) b s | yes _ with enabled s
... | [] = exhausted
... | _ ∷ _ = branching

-- The finite raw alphabet and enabled events use the bridge's lossless labels.
open import Process_Trees using (ExtI)
open import Data.Unit using (⊤)
open import Semantics.LTS {E = Raw.Channel} {I = ExtI Raw.Channel} using (Event√)
open import Semantics.Refusals {E = Raw.Channel} {I = ExtI Raw.Channel} using (Offers; Refuses)
rawAlphabet : List (Event√ ⊤)
rawAlphabet = map Raw.label alphabet
enabledEvents : State → List (Event√ ⊤)
enabledEvents s = map (λ where (a , t) → Raw.label a) (enabled s)
events-sound : ∀ {s e} → e ∈ enabledEvents s → Offers (Raw.Process s) e
events-sound {s} p with map-out {A = Action × State} (λ where (a , t) → Raw.label a) {xs = enabled s} p
... | (a , t) , member , refl = Raw.Process t , Raw.step-intro (Data.Product.proj₂ (enabled-sound member))
events-complete : ∀ {s e} → e ∈ rawAlphabet → Offers (Raw.Process s) e → e ∈ enabledEvents s
events-complete {s} member offer with map-out Raw.label member
... | a , covered , refl with offer
... | P , edge with Raw.step-inv edge
... | t , eq , endpoint = map-in (λ where (a , t) → Raw.label a) (enabled-complete covered eq)

-- A carrier action absent from the enabled list has the existing raw refusal.
absent-refusal : ∀ {s a} → a ∈ alphabet →
  (∀ t → (a , t) ∈ enabled s → Data.Empty.⊥) →
  Refuses (Raw.Process s) (λ e → e ≡ Raw.label a)
absent-refusal {s} {a} member absent = Raw.singleton-refusal
  (Raw.not-offered-disabled reject)
  where
  reject : Offers (Raw.Process s) (Raw.label a) → Data.Empty.⊥
  reject (P , edge) with Raw.step-inv edge
  ... | t , eq , endpoint = absent t (enabled-complete member eq)

-- Report every boundary, including the enabled successor rejected by allocation.
-- Prefixes are retained so a cutoff can be replayed, and never called deadlock.
frontiers : ℕ → ℕ → State → List (List Action × State × Frontier)
frontiers n b s with allocated s ≤? b
... | no _ = ([] , s , allocation-cutoff) ∷ []
frontiers zero b s | yes _ = ([] , s , depth-cutoff) ∷ []
frontiers (suc n) b s | yes _ with enabled s
... | [] = ([] , s , exhausted) ∷ []
... | edges@(_ ∷ _) = concatMap
  (λ { (a , t) → map (λ { (as , u , report) → (a ∷ as) , u , report })
    (frontiers n b t) }) edges

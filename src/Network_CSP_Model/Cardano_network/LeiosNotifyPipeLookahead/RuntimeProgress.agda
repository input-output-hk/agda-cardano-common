{-# OPTIONS --safe #-}

-- Runtime waiting/failure is separate from successful finite driver operations.
module Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress
  (Notification Return : Set) where

open import Data.Nat using (ℕ; suc; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.List using (List; []; _++_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Induction.WellFounded using (Acc; acc)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification Return as Cost
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Work
open import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification Return
  using (Move; LocalProgress; preserve; ready; decreases; stays; rows; prepend)

-- These failures are outcomes, not successful transitions or evidence of completion.
data Fault : Set where
  callback channel traceHook canceledThread arithmetic : Fault

-- A tick may wait arbitrarily; advance always carries one actual source operation.
data Tick (p : S.Contract) (s : D.State) : Set where
  waiting : Tick p s
  advance : ∀ {t} → Move p s t → Tick p s
  failed : Fault → Tick p s
  halted : Tick p s

-- Only a successful operation changes the protocol state at this abstraction boundary.
after : ∀ {p s} → Tick p s → D.State
after {s = s} waiting = s
after (advance {t = t} _) = t
after {s = s} (failed _) = s
after {s = s} halted = s

-- The time index records runtime observations, including periods with no model operation.
record Execution (p : S.Contract) : Set where
  field
    state : ℕ → D.State
    tick : (n : ℕ) → Tick p (state n)
    link : ∀ n → state (suc n) ≡ after (tick n)
open Execution public

-- A response may be a successful operation, an exception, or a terminal observation.
data Returned {p s} : Tick p s → Set where
  advanced : ∀ {t} {move : Move p s t} → Returned (advance move)
  faulted : ∀ {fault} → Returned (failed fault)
  stopped : Returned halted

-- Finite waiting is inductive; infinite waiting cannot supply this evidence.
data Response {p} (ex : Execution p) (n : ℕ) : Set where
  now : Returned (tick ex n) → Response ex n
  later : tick ex n ≡ waiting → Response ex (suc n) → Response ex n

-- Fault exclusion is an explicit assumption about the execution, not the model.
NoFailure : ∀ {p} → Execution p → Set
NoFailure ex = ∀ n fault → tick ex n ≡ failed fault → ⊥

-- A terminal observation is justified only when no successful model operation is enabled.
Maximal : ∀ {p} → Execution p → Set
Maximal {p} ex = ∀ n → tick ex n ≡ halted → ∀ {t} → Move p (state ex n) t → ⊥

-- This aggregate responsiveness excludes scheduler/channel/callback/hook starvation.
Responsive : ∀ {p} → (D.State → Set) → Execution p → Set
Responsive Target ex = ∀ n → ¬ Target (state ex n) → Response ex n

-- A waiting observation preserves the source state exactly.
wait-state : ∀ {p} (ex : Execution p) {n} → tick ex n ≡ waiting → state ex (suc n) ≡ state ex n
wait-state ex {n} eq = trans (link ex n) (cong after eq)

-- One eventual advance names its actual later time and its exact successful move.
record Next {p} (ex : Execution p) (n : ℕ) : Set where
  constructor next
  field
    index : ℕ
    strictly-later : n < index
    operation : Move p (state ex n) (state ex index)
open Next public

-- Finite waiting, no failure and no premature halt force a real enabled advance.
next-operation : ∀ {p} (ex : Execution p) → NoFailure ex → Maximal ex →
  ∀ {n} → Response ex n → (Σ[ t ∈ D.State ] Move p (state ex n) t) → Next ex n
next-operation ex noFailure maximal {n} (now returned) enabled with tick ex n in eq
... | advance move = next (suc n) (s≤s ≤-refl)
  (subst (Move _ (state ex n)) (sym (trans (link ex n) (cong after eq))) move)
... | failed fault = ⊥-elim (noFailure n fault eq)
... | halted = ⊥-elim (maximal n eq (Data.Product.proj₂ enabled))
next-operation ex noFailure maximal {n} (later eq response) (t , move)
  with next-operation ex noFailure maximal response
    (t , subst (λ s → Move _ s t) (sym (wait-state ex eq)) move)
... | next k laterTime operation = next k (≤-trans (n≤1+n (suc n)) laterTime)
  (subst (λ s → Move _ s (state ex k)) (wait-state ex eq) operation)

-- Eventual completion exposes both the runtime time and a bounded actual model path.
record Eventual {p} (Target : D.State → Set) (ex : Execution p) (n : ℕ) : Set where
  constructor eventual
  field
    index : ℕ
    later-or-now : n ≤ index
    events : List D.Event
    execution : D.Run p (state ex n) events (state ex index)
    reached : Target (state ex index)
    bounded : Work.steps execution ≤ Cost.rank (state ex n)
open Eventual public

-- Local model progress and external responsiveness are separate theorem parameters.
module With (p : S.Contract) (Target Invariant : D.State → Set)
  (progress : LocalProgress p Target Invariant) (ex : Execution p)
  (responsive : Responsive Target ex) (noFailure : NoFailure ex) (maximal : Maximal ex) where

  -- Every actual advance consumes potential, even when runtime waiting has no time bound.
  from-rank : ∀ n → Invariant (state ex n) → Work.BothStopping (state ex n) →
    Acc _<_ (Cost.rank (state ex n)) → Eventual Target ex n
  from-rank n invariant both (acc smaller) with ready progress invariant both
  ... | inj₁ reached = eventual n ≤-refl [] D.stop reached
    (Work.bounded {p = p} {s = state ex n} D.stop both)
  ... | inj₂ (unfinished , enabled)
    with next-operation ex noFailure maximal (responsive n unfinished) enabled
  ...   | next k laterTime move
    with from-rank k (preserve progress move invariant) (stays move both) (smaller (decreases move both))
  ...     | eventual j laterTime′ events run reached bounded =
    eventual j (≤-trans (Data.Nat.Properties.<⇒≤ laterTime) laterTime′)
      (rows move ++ events) (prepend move run) reached (Work.bounded (prepend move run) both)

  -- This is conditional liveness of the given execution, not a conclusion from finite replay.
  complete : ∀ n → Invariant (state ex n) → Work.BothStopping (state ex n) → Eventual Target ex n
  complete n invariant both = from-rank n invariant both (<-wellFounded (Cost.rank (state ex n)))

{-# OPTIONS --guardedness #-}

-- Original c2 for the owned-callers variant. At every initialized finished
-- outer run, both outbound call-frame lookups are nothing for every worker.
-- This is finite-run safety; shutdown progress and source-code refinement are
-- not asserted. All source theorems apply through V.outer-restriction.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedCallers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import ConnectionManagement.Domain using (HandleId)
open import Data.Nat using (ℕ)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Variants.OwnedCallers as Variant
import ConnectionManagement.Properties.OwnedCallersBase as Base
import ConnectionManagement.Properties.OwnedCallersSelection as SelectionFacts
import ConnectionManagement.Properties.ForeignFrames as ForeignFacts
open Base isBearerClosed isIOManagerError using (module K; NF)
private module VariantBase = Variant isBearerClosed isIOManagerError

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  open VariantBase.Protocols canInitiate using (module T; module Outer)
  module V = VariantBase.Protocols canInitiate
  private
    module Selection = SelectionFacts.Protocols isBearerClosed isIOManagerError canInitiate
  open ForeignFacts.Protocols isBearerClosed isIOManagerError canInitiate using (ForeignFrames; foreign-frames)

  -- One guarded outer step either advances the guarded inner runtime or keeps it.
  outer-step-inv : ∀ a s {t} → V.outerStep′ a s ≡ just t → Selection.Inv (Outer.inner s) → Selection.Inv (Outer.inner t)
  outer-step-inv (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.inside)) eq held with V.advance′ a s in stepped
  ... | nothing = case eq of λ ()
  ... | just s′ = case just-injective eq of λ { refl → Selection.advance-inv a s stepped held }
  outer-step-inv (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.cancelling)) eq held = case eq of λ ()
  outer-step-inv (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.finished)) eq held = case eq of λ ()
  outer-step-inv (Outer.relaysAct a) (Outer.outer s r) eq held with RR.step (Outer.runtimeReturned s) a r
  ... | nothing = case eq of λ ()
  ... | just r′ = case just-injective eq of λ { refl → held }

  -- Reach and NoForeign are invariant over every executable variant outer run.
  outer-inv : ∀ {s as t} → V.OuterRuns′ s as t → Selection.Inv (Outer.inner s) → Selection.Inv (Outer.inner t)
  outer-inv V.outer-done′ held = held
  outer-inv (V.outer-next′ {s = s} {a = a} eq rest) held = outer-inv rest (outer-step-inv a s eq held)

  -- Explicit initialized invariant, without requiring a finished shutdown.
  no-foreign : ∀ {c₀ g start r as final r′} → T.initialize (O.initial c₀) g ≡ just start →
    V.OuterRuns′ (Outer.outer start r) as (Outer.outer final r′) → NF (T.base final)
  no-foreign {c₀} {g} initialized path = proj₂ (outer-inv path (Selection.initial-inv c₀ g initialized))

  -- Both exact original c2 clauses, quantified over every worker.
  NoFrames : T.Runtime → Set
  NoFrames final = (∀ w → lookup w (O.acquiring (T.sourceOf final)) ≡ nothing) ×
    (∀ w → lookup w (O.releasing (T.sourceOf final)) ≡ nothing)

  -- Restated c2 says each final frame is Foreign; the variant invariant excludes
  -- that alternative. The initialized and finished-relays premises are unchanged.
  no-frames : ∀ {c₀ g start scheduled as final t} → T.initialize (O.initial c₀) g ≡ just start →
    V.OuterRuns′ (Outer.outer start (RR.initial scheduled)) as (Outer.outer final (RR.relaysState t RR.finished)) →
    NoFrames final
  no-frames {final = final} initialized path = acquire-empty , release-empty
    where
    held = no-foreign initialized path
    final-foreign = foreign-frames initialized (V.outer-restriction path)
    acquire-empty : ∀ w → lookup w (O.acquiring (T.sourceOf final)) ≡ nothing
    acquire-empty w with lookup w (O.acquiring (T.sourceOf final)) in found
    ... | nothing = refl
    ... | just f = ⊥-elim (held w (inj₁ (cong is-just found)) (proj₂ (ForeignFrames.acquiring final-foreign w f found)))
    release-empty : ∀ w → lookup w (O.releasing (T.sourceOf final)) ≡ nothing
    release-empty w with lookup w (O.releasing (T.sourceOf final)) in found
    ... | nothing = refl
    ... | just f = ⊥-elim (held w (inj₂ (cong is-just found)) (proj₂ (ForeignFrames.releasing final-foreign w f found)))

  -- An inexpensive event-label policy is enough to certify concrete source runs.
  outerOnly : Outer.OuterAction → Bool
  outerOnly (Outer.innerAct a) = V.eventOnly a
  outerOnly (Outer.relaysAct _) = true

  -- Conjunction over labels needs no evaluation of concrete composed states.
  everyOwned : List Outer.OuterAction → Bool
  everyOwned [] = true
  everyOwned (a ∷ as) = outerOnly a ∧ everyOwned as

  -- Boolean conjunction provides the head and tail policy facts.
  and-true : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
  and-true true true refl = refl , refl
  and-true true false ()
  and-true false b ()

  -- Each allowed event label constrains every selected shared action.
  label-policy : ∀ a s → outerOnly a ≡ true → V.outerAllowed a s
  label-policy (Outer.innerAct a) s ok = Selection.event-policy a (Outer.inner s) ok
  label-policy (Outer.relaysAct a) s ok = tt

  -- This works even when the original execution witness is abstract/opaque.
  source-policy : ∀ {s as t} → everyOwned as ≡ true → (path : Outer.Executes s as t) → V.Allowed path
  source-policy ok Outer.done = tt
  source-policy {as = a ∷ as} ok (Outer.next {s = s} eq rest) with and-true (outerOnly a) (everyOwned as) ok
  ... | head , tail = label-policy a s head , source-policy tail rest

  -- Every guarded outer edge satisfies the corresponding event-label policy.
  outer-label : ∀ a s {t} → V.outerStep′ a s ≡ just t → outerOnly a ≡ true
  outer-label (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.inside)) eq with V.advance′ a s in stepped
  ... | nothing = case eq of λ ()
  ... | just s′ = V.advance-event-policy a s stepped
  outer-label (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.cancelling)) eq = case eq of λ ()
  outer-label (Outer.innerAct a) (Outer.outer s (RR.relaysState r RR.finished)) eq = case eq of λ ()
  outer-label (Outer.relaysAct a) s eq = refl

  -- Necessary event-label policy refutes the inserted-begin counterexample run.
  run-policy : ∀ {s as t} → V.OuterRuns′ s as t → everyOwned as ≡ true
  run-policy V.outer-done′ = refl
  run-policy (V.outer-next′ {s = s} {a = a} eq rest) rewrite outer-label a s eq | run-policy rest = refl

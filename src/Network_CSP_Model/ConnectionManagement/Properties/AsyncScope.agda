{-# OPTIONS --guardedness #-}

-- A finished physical-scope coordinator certifies all four joins. This does
-- not certify the adapter's local cleanup or the remaining CM/server scopes.
module ConnectionManagement.Properties.AsyncScope where

import Data.Empty
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import ConnectionManagement.Rules.AsyncScope as S

-- Expose actor-specific evidence rather than only a Boolean close flag.
AllJoined : S.State → Set
AllJoined s = S.threads s S.churn ≡ S.joined ×
  S.threads s S.governor ≡ S.joined ×
  S.threads s S.localRoot ≡ S.joined ×
  S.threads s S.ledger ≡ S.joined

and-left : ∀ a b → a ∧ b ≡ true → a ≡ true
and-left false b ()
and-left true b eq = refl
and-right : ∀ a b → a ∧ b ≡ true → b ≡ true
and-right false b ()
and-right true b eq = eq
joined-evidence : ∀ phase → S.isJoined phase ≡ true → phase ≡ S.joined
joined-evidence S.running ()
joined-evidence S.cancelRequested ()
joined-evidence S.cancelDelivered ()
joined-evidence S.bodyUnwinding ()
joined-evidence S.bodyExited ()
joined-evidence S.resultAvailable ()
joined-evidence S.joined eq = refl

-- The final Boolean check corresponds exactly to four physical joined phases.
all-joined-evidence : ∀ s → S.allJoined s ≡ true → AllJoined s
all-joined-evidence s eq =
  joined-evidence _ (and-left c (g ∧ l ∧ r) eq) ,
  joined-evidence _ (and-left g (l ∧ r) tail₁) ,
  joined-evidence _ (and-left l r tail₂) ,
  joined-evidence _ (and-right l r tail₂)
  where
  c g l r : Bool
  c = S.isJoined (S.threads s S.churn)
  g = S.isJoined (S.threads s S.governor)
  l = S.isJoined (S.threads s S.localRoot)
  r = S.isJoined (S.threads s S.ledger)
  tail₁ : g ∧ l ∧ r ≡ true
  tail₁ = and-right c (g ∧ l ∧ r) eq
  tail₂ : l ∧ r ≡ true
  tail₂ = and-right g (l ∧ r) tail₁

-- An ordinary transition that retains the cursor cannot manufacture closure.
same-cursor : ∀ s c g l r issued {s′} →
  just (S.scopeState c g l r (S.cursor s) issued) ≡ just s′ →
  S.cursor s′ ≡ S.finishedScope →
  (S.cursor s ≡ S.finishedScope → Data.Empty.⊥) → AllJoined s′
same-cursor s c g l r issued eq closed notClosed with just-injective eq
... | refl = Data.Empty.⊥-elim (notClosed closed)

next-not-finished : ∀ actor → S.nextCursor actor ≡ S.finishedScope → Data.Empty.⊥
next-not-finished S.churn ()
next-not-finished S.governor ()
next-not-finished S.localRoot ()
next-not-finished S.ledger ()

-- Only explicit finishClose introduces the finished cursor; its source guard
-- consumes the four join certificates. No postcondition guard is added to step.
advance-certifies : ∀ gate action s {s′} →
  (S.cursor s ≡ S.finishedScope → Data.Empty.⊥) →
  S.advance gate action s ≡ just s′ → S.cursor s′ ≡ S.finishedScope → AllJoined s′
advance-certifies gate S.beginUnwind s notClosed eq closed with S.cursor s
advance-certifies gate S.beginUnwind s notClosed eq closed | S.openScope with just-injective eq
... | refl with closed
...   | ()
advance-certifies gate S.beginUnwind s notClosed eq closed | S.closing actor with eq
... | ()
advance-certifies gate S.beginUnwind s notClosed eq closed | S.readyToFinish with eq
... | ()
advance-certifies gate S.beginUnwind s notClosed eq closed | S.finishedScope with eq
... | ()
advance-certifies gate S.requestCancel s notClosed eq closed with S.cursor s in current | S.requestIssued s
advance-certifies gate S.requestCancel s notClosed eq closed | S.closing actor | false with S.threads s actor
advance-certifies gate S.requestCancel s notClosed eq closed | S.closing actor | false | S.running = same-cursor s _ _ _ _ true eq closed (λ e → notClosed (trans (sym current) e))
advance-certifies gate S.requestCancel s notClosed eq closed | S.closing actor | false | S.cancelRequested = same-cursor s _ _ _ _ true eq closed (λ e → notClosed (trans (sym current) e))
advance-certifies gate S.requestCancel s notClosed eq closed | S.closing actor | false | S.cancelDelivered = same-cursor s _ _ _ _ true eq closed (λ e → notClosed (trans (sym current) e))
advance-certifies gate S.requestCancel s notClosed eq closed | S.closing actor | false | S.bodyUnwinding = same-cursor s _ _ _ _ true eq closed (λ e → notClosed (trans (sym current) e))
advance-certifies gate S.requestCancel s notClosed eq closed | S.closing actor | false | S.bodyExited = same-cursor s _ _ _ _ true eq closed (λ e → notClosed (trans (sym current) e))
advance-certifies gate S.requestCancel s notClosed eq closed | S.closing actor | false | S.resultAvailable = same-cursor s _ _ _ _ true eq closed (λ e → notClosed (trans (sym current) e))
advance-certifies gate S.requestCancel s notClosed eq closed | S.closing actor | false | S.joined with eq
... | ()
advance-certifies gate S.requestCancel s notClosed eq closed | S.openScope | issued with eq
... | ()
advance-certifies gate S.requestCancel s notClosed eq closed | S.closing actor | true with eq
... | ()
advance-certifies gate S.requestCancel s notClosed eq closed | S.readyToFinish | issued with eq
... | ()
advance-certifies gate S.requestCancel s notClosed eq closed | S.finishedScope | issued with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed with S.cursor s in current | S.requestIssued s
advance-certifies gate S.deliverCancel s notClosed eq closed | S.closing actor | true with S.threads s actor
advance-certifies gate S.deliverCancel s notClosed eq closed | S.closing actor | true | S.running with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed | S.closing actor | true | S.cancelRequested = same-cursor s _ _ _ _ (S.requestIssued s) eq closed (λ e → notClosed (trans (sym current) e))
advance-certifies gate S.deliverCancel s notClosed eq closed | S.closing actor | true | S.cancelDelivered with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed | S.closing actor | true | S.bodyUnwinding with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed | S.closing actor | true | S.bodyExited with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed | S.closing actor | true | S.resultAvailable with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed | S.closing actor | true | S.joined with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed | S.openScope | issued with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed | S.closing actor | false with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed | S.readyToFinish | issued with eq
... | ()
advance-certifies gate S.deliverCancel s notClosed eq closed | S.finishedScope | issued with eq
... | ()
advance-certifies gate (S.beginFailure actor) s notClosed eq closed with S.threads s actor
advance-certifies gate (S.beginFailure actor) s notClosed eq closed | S.running = same-cursor s _ _ _ _ (S.requestIssued s) eq closed notClosed
advance-certifies gate (S.beginFailure actor) s notClosed eq closed | S.cancelRequested = same-cursor s _ _ _ _ (S.requestIssued s) eq closed notClosed
advance-certifies gate (S.beginFailure actor) s notClosed eq closed | S.cancelDelivered with eq
... | ()
advance-certifies gate (S.beginFailure actor) s notClosed eq closed | S.bodyUnwinding with eq
... | ()
advance-certifies gate (S.beginFailure actor) s notClosed eq closed | S.bodyExited with eq
... | ()
advance-certifies gate (S.beginFailure actor) s notClosed eq closed | S.resultAvailable with eq
... | ()
advance-certifies gate (S.beginFailure actor) s notClosed eq closed | S.joined with eq
... | ()
advance-certifies gate (S.bodyExit actor) s notClosed eq closed with S.exitAllowed actor gate Data.Bool.∧ S.canExit (S.threads s actor)
advance-certifies gate (S.bodyExit actor) s notClosed eq closed | false with eq
... | ()
advance-certifies gate (S.bodyExit actor) s notClosed eq closed | true = same-cursor s _ _ _ _ (S.requestIssued s) eq closed notClosed
advance-certifies gate (S.publishResult actor) s notClosed eq closed with S.threads s actor
advance-certifies gate (S.publishResult actor) s notClosed eq closed | S.running with eq
... | ()
advance-certifies gate (S.publishResult actor) s notClosed eq closed | S.cancelRequested with eq
... | ()
advance-certifies gate (S.publishResult actor) s notClosed eq closed | S.cancelDelivered with eq
... | ()
advance-certifies gate (S.publishResult actor) s notClosed eq closed | S.bodyUnwinding with eq
... | ()
advance-certifies gate (S.publishResult actor) s notClosed eq closed | S.bodyExited = same-cursor s _ _ _ _ (S.requestIssued s) eq closed notClosed
advance-certifies gate (S.publishResult actor) s notClosed eq closed | S.resultAvailable with eq
... | ()
advance-certifies gate (S.publishResult actor) s notClosed eq closed | S.joined with eq
... | ()
advance-certifies gate S.join s notClosed eq closed with S.cursor s | S.requestIssued s
advance-certifies gate S.join s notClosed eq closed | S.closing actor | true with S.threads s actor
advance-certifies gate S.join s notClosed eq closed | S.closing actor | true | S.running with eq
... | ()
advance-certifies gate S.join s notClosed eq closed | S.closing actor | true | S.cancelRequested with eq
... | ()
advance-certifies gate S.join s notClosed eq closed | S.closing actor | true | S.cancelDelivered with eq
... | ()
advance-certifies gate S.join s notClosed eq closed | S.closing actor | true | S.bodyUnwinding with eq
... | ()
advance-certifies gate S.join s notClosed eq closed | S.closing actor | true | S.bodyExited with eq
... | ()
advance-certifies gate S.join s notClosed eq closed | S.closing actor | true | S.resultAvailable with just-injective eq
... | refl = Data.Empty.⊥-elim (next-not-finished actor closed)
advance-certifies gate S.join s notClosed eq closed | S.closing actor | true | S.joined with eq
... | ()
advance-certifies gate S.join s notClosed eq closed | S.openScope | issued with eq
... | ()
advance-certifies gate S.join s notClosed eq closed | S.closing actor | false with eq
... | ()
advance-certifies gate S.join s notClosed eq closed | S.readyToFinish | issued with eq
... | ()
advance-certifies gate S.join s notClosed eq closed | S.finishedScope | issued with eq
... | ()
advance-certifies gate S.finishClose s notClosed eq closed with S.cursor s | S.allJoined s in all
advance-certifies gate S.finishClose s notClosed eq closed | S.readyToFinish | true with just-injective eq
... | refl = all-joined-evidence s all
advance-certifies gate S.finishClose s notClosed eq closed | S.readyToFinish | false with eq
... | ()
advance-certifies gate S.finishClose s notClosed eq closed | S.openScope | joined with eq
... | ()
advance-certifies gate S.finishClose s notClosed eq closed | S.closing actor | joined with eq
... | ()
advance-certifies gate S.finishClose s notClosed eq closed | S.finishedScope | joined with eq
... | ()

open-not-finished : S.openScope ≡ S.finishedScope → Data.Empty.⊥
open-not-finished ()
closing-not-finished : ∀ actor → S.closing actor ≡ S.finishedScope → Data.Empty.⊥
closing-not-finished actor ()
ready-not-finished : S.readyToFinish ≡ S.finishedScope → Data.Empty.⊥
ready-not-finished ()

-- A successful step from an unfinished scope can close only by the preceding
-- finish transition. Already finished states admit no further transitions.
step-certifies : ∀ gate action s {s′} → S.step gate action s ≡ just s′ →
  S.cursor s′ ≡ S.finishedScope → AllJoined s′
step-certifies gate action s eq closed with S.cursor s in cursor
... | S.finishedScope with eq
...   | ()
step-certifies gate action s eq closed | S.openScope = advance-certifies gate action s (λ e → open-not-finished (trans (sym cursor) e)) eq closed
step-certifies gate action s eq closed | S.closing actor = advance-certifies gate action s (λ e → closing-not-finished actor (trans (sym cursor) e)) eq closed
step-certifies gate action s eq closed | S.readyToFinish = advance-certifies gate action s (λ e → ready-not-finished (trans (sym cursor) e)) eq closed

Valid : S.State → Set
Valid s = S.cursor s ≡ S.finishedScope → AllJoined s
initial-valid : Valid S.initial
initial-valid ()

-- Any finite execution retains the certificate; no termination is asserted.
exec-preserves : ∀ {s actions s′} → S.Executes s actions s′ → Valid s → Valid s′
exec-preserves S.done valid = valid
exec-preserves (S.next {s = s} {a = action} {gate = gate} eq path) valid =
  exec-preserves path (step-certifies gate action s eq)
from-initial : ∀ {actions s} → S.Executes S.initial actions s →
  S.cursor s ≡ S.finishedScope → AllJoined s
from-initial path = exec-preserves path initial-valid

-- Governor local-body exit requires the adapter's own-pool completion check.
governor-exit-without-pool-refused : ∀ s → S.step false (S.bodyExit S.governor) s ≡ nothing
governor-exit-without-pool-refused s with S.cursor s
... | S.finishedScope = refl
... | S.openScope = refl
... | S.closing actor = refl
... | S.readyToFinish = refl

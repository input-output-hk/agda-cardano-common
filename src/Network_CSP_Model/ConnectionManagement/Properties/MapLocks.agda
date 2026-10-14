{-# OPTIONS --guardedness #-}

-- Primitive guarantees only: these do not establish eventual lock release or
-- reachability/source refinement of the future combined subsystem.
module ConnectionManagement.Properties.MapLocks where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.CM

-- No second owner can acquire a taken map.
taken-blocks : ∀ w owner heap n →
  takeMap w (cmStore (taken owner) heap n) ≡ nothing
taken-blocks w owner heap n = refl

-- Restoring the saved map never rolls back the current entry heap.
restore-preserves-heap : ∀ l c {c′} →
  restoreMap l c ≡ just c′ → entries c′ ≡ entries c
restore-preserves-heap l (cmStore (full m) h n) ()
restore-preserves-heap l (cmStore (taken w) h n) eq with owner l ≟ w
... | no _ = case eq of λ ()
... | yes _ = sym (cong entries (just-injective eq))

-- Neither putting a new map nor restoration can release a different owner.
other-owner-cannot-put : ∀ l m w h n → owner l ≢ w →
  putMap l m (cmStore (taken w) h n) ≡ nothing
other-owner-cannot-put l m w h n neq with owner l ≟ w
... | no _ = refl
... | yes eq = ⊥-elim (neq eq)

-- A write through a captured entry reference leaves map ownership unchanged.
captured-write-preserves-lock : ∀ e st c {c′} →
  writeCaptured e st c ≡ just c′ → mapCell c′ ≡ mapCell c
captured-write-preserves-lock e st c eq with lookup e (entries c)
... | nothing = case eq of λ ()
... | just _ = sym (cong mapCell (just-injective eq))

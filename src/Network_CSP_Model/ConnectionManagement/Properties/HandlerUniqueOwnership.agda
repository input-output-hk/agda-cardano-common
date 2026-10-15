{-# OPTIONS --guardedness #-}

-- Preservation of the SAME executable uniqueness predicate used by diagnostics.
module ConnectionManagement.Properties.HandlerUniqueOwnership where

open import Data.Bool using (true; false; not; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.HandlerCapture using (lookup-put-other)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Properties.HandlerEvolution as E
import ConnectionManagement.Properties.HandlerValidity as V

Unique : L.Runtime → Set
Unique rt = V.uniqueOwners rt ≡ true

-- A phase write cannot affect the mux-identity census, even for malformed stores.
phase-hasMux : ∀ mid w f p rt → lookup w rt ≡ just f →
  L.hasMux mid (L.setPhase w f p rt) ≡ L.hasMux mid rt
phase-hasMux mid w f p [] ()
phase-hasMux mid w f p ((q , old) ∷ xs) found with w ≟ q
... | yes refl with just-injective found
...   | refl with mid ≟ L.capturedMux f
...     | yes _ = refl
...     | no _ = refl
phase-hasMux mid w f p ((q , old) ∷ xs) found | no _ with mid ≟ L.capturedMux old
... | yes _ = refl
... | no _ = phase-hasMux mid w f p xs found

-- Complete uniqueness is unchanged by phase updates, not merely preserved.
phase-owners : ∀ w f p rt → lookup w rt ≡ just f →
  V.uniqueOwners (L.setPhase w f p rt) ≡ V.uniqueOwners rt
phase-owners w f p [] ()
phase-owners w f p ((q , old) ∷ xs) found with w ≟ q
... | yes refl with just-injective found
...   | refl with lookup w xs
...     | just _ = refl
...     | nothing = refl
phase-owners w f p ((q , old) ∷ xs) found | no neq
  rewrite lookup-put-other w q (record f { phase = p }) xs (λ eq → neq (sym eq))
  with lookup q xs
... | just _ = refl
... | nothing rewrite phase-hasMux (L.capturedMux old) w f p xs found =
  cong (λ b → not (L.hasMux (L.capturedMux old) xs) ∧ b) (phase-owners w f p xs found)

-- Adding a different captured mux cannot invalidate an existing absence test.
put-absent-mux : ∀ mid w f rt → L.hasMux mid rt ≡ false → mid ≢ L.capturedMux f →
  L.hasMux mid (put w f rt) ≡ false
put-absent-mux mid w f [] absent neq with mid ≟ L.capturedMux f
... | yes eq = ⊥-elim (neq eq)
... | no _ = refl
put-absent-mux mid w f ((q , old) ∷ xs) absent neq with w ≟ q
... | yes _ with mid ≟ L.capturedMux old | mid ≟ L.capturedMux f
...   | yes _ | _ = case absent of λ ()
...   | no _ | yes eq = ⊥-elim (neq eq)
...   | no _ | no _ = absent
put-absent-mux mid w f ((q , old) ∷ xs) absent neq | no _ with mid ≟ L.capturedMux old
... | yes _ = case absent of λ ()
... | no _ = put-absent-mux mid w f xs absent neq

-- Attachment must use both guards: absent worker AND absent captured mux.
fresh-owners : ∀ w f rt → lookup w rt ≡ nothing →
  L.hasMux (L.capturedMux f) rt ≡ false → Unique rt → Unique (put w f rt)
fresh-owners w f [] absent unused unique = refl
fresh-owners w f ((q , old) ∷ xs) absent unused unique
  with w ≟ q | L.capturedMux f ≟ L.capturedMux old
... | yes _ | _ = case absent of λ ()
... | no _ | yes _ = case unused of λ ()
... | no neq | no apart with lookup q xs in qAbsent | L.hasMux (L.capturedMux old) xs in qUnused
...   | just _ | _ = case unique of λ ()
...   | nothing | true rewrite qUnused = case unique of λ ()
...   | nothing | false
  rewrite lookup-put-other w q f xs (λ eq → neq (sym eq))
        | qAbsent
        | qUnused
        | put-absent-mux (L.capturedMux old) w f xs qUnused (λ eq → apart (sym eq)) =
  fresh-owners w f xs absent unused unique

evolution-preserves : ∀ {rt rt′} → E.Evolution rt rt′ → Unique rt → Unique rt′
evolution-preserves E.unchanged unique = unique
evolution-preserves (E.attached w f rt absent unused) = fresh-owners w f rt absent unused
evolution-preserves (E.phaseChanged w f p rt found) unique = trans (phase-owners w f p rt found) unique

{-# OPTIONS --guardedness #-}

-- Ownership-preserving acquisition and release of the map by the implemented
-- admission and cleanup continuations. Heap validity is a separate obligation.
module ConnectionManagement.Properties.OwnershipMapSteps where

open import Data.List using ([]; _∷_; _++_; concatMap)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipCensus
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup
open import ConnectionManagement.Machine using (world; advance; admissionStep; cleanupStep)

admissionState : WorkerId → AdmissionWorker → AdmissionPC → MapCell → State → State
admissionState w a p cell s = Server.setPC w a p (record s { cm = record (cm s) { mapCell = cell } })

cleanupState : WorkerId → CleanupPC → MapCell → State → State
cleanupState w p cell s = Cleanup.setCleanup w p (record s { cm = record (cm s) { mapCell = cell } })

admission-splice : ∀ w a p cell s → lookup w (admissions s) ≡ just a →
  Splice (claim w (admissionLease (pc a))) (claim w (admissionLease p))
    (claims s) (claims (admissionState w a p cell s))
admission-splice w a p cell s found = suffix-splice (concatMap cleanupClaim (cleanups s))
  (put-splice admissionClaim w a (record a { pc = p }) (admissions s) found)

cleanup-splice : ∀ w old p cell s → lookup w (cleanups s) ≡ just old →
  Splice (claim w (cleanupLease old)) (claim w (cleanupLease p))
    (claims s) (claims (cleanupState w p cell s))
cleanup-splice w old p cell s found = prefix-splice (concatMap admissionClaim (admissions s))
  (put-splice cleanupClaim w old p (cleanups s) found)

admission-acquire : ∀ w a p m s → lookup w (admissions s) ≡ just a →
  admissionLease (pc a) ≡ nothing → admissionLease p ≡ just (lease w m) →
  mapCell (cm s) ≡ full m → Ownership s → Ownership (admissionState w a p (taken w) s)
admission-acquire w a p m s found old new cell own
  with admission-splice w a p (taken w) s found
... | splice rewrite old | new | cell = lease w m , acquire-census (w , lease w m) splice own , refl

cleanup-acquire : ∀ w old p m s → lookup w (cleanups s) ≡ just old →
  cleanupLease old ≡ nothing → cleanupLease p ≡ just (lease w m) →
  mapCell (cm s) ≡ full m → Ownership s → Ownership (cleanupState w p (taken w) s)
cleanup-acquire w old p m s found oldEq new cell own
  with cleanup-splice w old p (taken w) s found
... | splice rewrite oldEq | new | cell = lease w m , acquire-census (w , lease w m) splice own , refl

admission-release : ∀ w a p l m v s → lookup w (admissions s) ≡ just a →
  admissionLease (pc a) ≡ just l → admissionLease p ≡ nothing →
  mapCell (cm s) ≡ taken v → Ownership s → Ownership (admissionState w a p (full m) s)
admission-release w a p l m v s found old new cell own
  with admission-splice w a p (full m) s found
... | splice rewrite old | new | cell with own
...   | held , single , ownerEq = release-census (w , l) (v , held) splice single

cleanup-release : ∀ w old p l m v s → lookup w (cleanups s) ≡ just old →
  cleanupLease old ≡ just l → cleanupLease p ≡ nothing →
  mapCell (cm s) ≡ taken v → Ownership s → Ownership (cleanupState w p (full m) s)
cleanup-release w old p l m v s found oldEq new cell own
  with cleanup-splice w old p (full m) s found
... | splice rewrite oldEq | new | cell with own
...   | held , single , ownerEq = release-census (w , l) (v , held) splice single

-- Source primitive outcomes determine the new map cell; these helpers preserve
-- the surrounding worker stores while changing the matching continuation.
import ConnectionManagement.Rules.CM as CM

admission-put : ∀ w a p l m s {c′} → lookup w (admissions s) ≡ just a →
  admissionLease (pc a) ≡ just l → admissionLease p ≡ nothing →
  CM.putMap l m (cm s) ≡ just c′ → Ownership s →
  Ownership (Server.setPC w a p (record s { cm = c′ }))
admission-put w a p l m s found old new eq own with mapCell (cm s) in cell
... | full _ = case eq of λ ()
... | taken v with owner l ≟ v
...   | no _ = case eq of λ ()
...   | yes _ with just-injective eq
...     | refl = admission-release w a p l m v s found old new cell (subst (λ c → Owns c (claims s)) (sym cell) own)

cleanup-put : ∀ w old p l m s {c′} → lookup w (cleanups s) ≡ just old →
  cleanupLease old ≡ just l → cleanupLease p ≡ nothing →
  CM.putMap l m (cm s) ≡ just c′ → Ownership s →
  Ownership (Cleanup.setCleanup w p (record s { cm = c′ }))
cleanup-put w old p l m s found oldEq new eq own with mapCell (cm s) in cell
... | full _ = case eq of λ ()
... | taken v with owner l ≟ v
...   | no _ = case eq of λ ()
...   | yes _ with just-injective eq
...     | refl = cleanup-release w old p l m v s found oldEq new cell (subst (λ c → Owns c (claims s)) (sym cell) own)

admission-take : ∀ w r s {l c′} → lookup w (admissions s) ≡ just (admissionWorker r acquireMap) →
  CM.takeMap w (cm s) ≡ just (l , c′) → Ownership s →
  Ownership (Server.setPC w (admissionWorker r acquireMap) (count l) (record s { cm = c′ }))
admission-take w r s found eq own with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with just-injective eq
...   | refl = admission-acquire w (admissionWorker r acquireMap) (count (lease w m)) m s found refl refl cell (subst (λ c → Owns c (claims s)) (sym cell) own)

cleanup-take : ∀ w s {l c′} → lookup w (cleanups s) ≡ just cleanupAcquire →
  CM.takeMap w (cm s) ≡ just (l , c′) → Ownership s →
  Ownership (Cleanup.setCleanup w (cleanupSelect l) (record s { cm = c′ }))
cleanup-take w s found eq own with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with just-injective eq
...   | refl = cleanup-acquire w cleanupAcquire (cleanupSelect (lease w m)) m s found refl refl cell (subst (λ c → Owns c (claims s)) (sym cell) own)

-- Publication releases the lease before either the counter or TIME_WAIT tail.
after-publish-no-lease : ∀ tail → cleanupLease (Cleanup.afterPublish tail) ≡ nothing
after-publish-no-lease countImmediately = refl
after-publish-no-lease (timeWait _) = refl

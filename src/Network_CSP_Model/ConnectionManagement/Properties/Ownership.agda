{-# OPTIONS --guardedness #-}

-- Exact lease census: a full map has no lease claimant; a taken map has exactly
-- one continuation claiming it, under the same worker as the captured lease.
module ConnectionManagement.Properties.Ownership where

open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State

-- Exhaustive cases force new continuations to make their lease status explicit.
admissionLease : AdmissionPC → Maybe Lease
admissionLease acquireMap = nothing
admissionLease (count l) = just l
admissionLease (prepare l) = just l
admissionLease (selectEntry l _) = just l
admissionLease (forkHandler l _ _) = just l
admissionLease (publish l _ _) = just l
admissionLease (reject l _) = just l
admissionLease (closeSocket _) = nothing
admissionLease (finished _) = nothing
admissionLease (countPublished _ _) = nothing
admissionLease (awaitHandshake _ _) = nothing
admissionLease (commitHandshake _ _) = nothing
admissionLease (countHandshake _) = nothing
admissionLease (notifyInbound _) = nothing
admissionLease (returnHandshake _) = nothing
admissionLease (completedHandshake _) = nothing
admissionLease impossibleHandshake = nothing

cleanupLease : CleanupPC → Maybe Lease
cleanupLease cleanupAcquire = nothing
cleanupLease (cleanupSelect l) = just l
cleanupLease (cleanupClose l _ _) = just l
cleanupLease (cleanupPublish l _ _) = just l
cleanupLease (cleanupRestore l _) = just l
cleanupLease (cleanupWaiting _) = nothing
cleanupLease (cleanupFinalize _ _) = nothing
cleanupLease (cleanupCount _) = nothing
cleanupLease (cleanupDone _) = nothing

Claim = WorkerId × Lease

claim : WorkerId → Maybe Lease → List Claim
claim w nothing = []
claim w (just l) = (w , l) ∷ []

admissionClaim : WorkerId × AdmissionWorker → List Claim
admissionClaim (w , a) = claim w (admissionLease (pc a))

cleanupClaim : WorkerId × CleanupPC → List Claim
cleanupClaim (w , p) = claim w (cleanupLease p)

claims : State → List Claim
claims s = concatMap admissionClaim (admissions s) ++ concatMap cleanupClaim (cleanups s)

Owns : MapCell → List Claim → Set
Owns (full _) cs = cs ≡ []
Owns (taken w) cs = Σ Lease (λ l → cs ≡ (w , l) ∷ [] × owner l ≡ w)

Ownership : State → Set
Ownership s = Owns (mapCell (cm s)) (claims s)

{-# OPTIONS --guardedness #-}

-- Equality of the six ownership observations is enough for context transport.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesObservation
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesContext as ContextFacts
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux)
private module V = ContextFacts isBearerClosed isIOManagerError

-- Copying equal observed fields is the identity even when all ignored fields differ.
observed-equal : ∀ k target →
  C.SubContext.jobs (C.subsystem target) ≡ C.SubContext.jobs (C.subsystem k) →
  C.SubContext.monitors (C.subsystem target) ≡ C.SubContext.monitors (C.subsystem k) →
  GP.Pool.handles (C.governorPool target) ≡ GP.Pool.handles (C.governorPool k) →
  C.monitors target ≡ C.monitors k →
  PS.Pool.handles (C.monitorPool target) ≡ PS.Pool.handles (C.monitorPool k) →
  C.unwinding target ≡ C.unwinding k → V.copy-observed k target ≡ target
observed-equal k (record
  { subsystem = record { jobs = rows; monitors = follows }
  ; governorPool = record { handles = gh }
  ; monitorPool = record { handles = mh }
  ; monitors = threads; unwinding = unwinds }) refl refl refl refl refl refl = refl

-- Transport both clauses and metadata along that exact observation equality.
observed-preserves : ∀ c k target → V.copy-observed k target ≡ target → Inv c k → Aux k → Inv c target × Aux target
observed-preserves c k target same inv aux = subst (Inv c) same (V.copy-inv c k target inv) ,
  subst Aux same (V.copy-aux k target aux)

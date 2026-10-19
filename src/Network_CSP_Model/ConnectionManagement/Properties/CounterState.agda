{-# OPTIONS --guardedness #-}

-- Collect all maps retained by the implemented continuations. Validity includes
-- saved and proposed maps while the global map cell is empty.
module ConnectionManagement.Properties.CounterState where

open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (proj₂)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Counters using (CounterReferences)

-- Enumerate constructors explicitly so future continuations require a decision.
admissionMaps : AdmissionPC → List ConnMap
admissionMaps acquireMap = []
admissionMaps (count l) = savedMap l ∷ []
admissionMaps (prepare l) = savedMap l ∷ []
admissionMaps (selectEntry l _) = savedMap l ∷ []
admissionMaps (forkHandler l _ _) = savedMap l ∷ []
admissionMaps (publish l _ _) = savedMap l ∷ []
admissionMaps (reject l _) = savedMap l ∷ []
admissionMaps (closeSocket _) = []
admissionMaps (finished _) = []
admissionMaps (countPublished _ _) = []
admissionMaps (awaitHandshake _ _) = []
admissionMaps (commitHandshake _ _) = []
admissionMaps (countHandshake _) = []
admissionMaps (notifyInbound _) = []
admissionMaps (returnHandshake _) = []
admissionMaps (completedHandshake _) = []
admissionMaps impossibleHandshake = []

cleanupMaps : CleanupPC → List ConnMap
cleanupMaps cleanupAcquire = []
cleanupMaps (cleanupSelect l) = savedMap l ∷ []
cleanupMaps (cleanupClose l proposed _) = savedMap l ∷ proposed ∷ []
cleanupMaps (cleanupPublish l proposed _) = savedMap l ∷ proposed ∷ []
cleanupMaps (cleanupRestore l _) = savedMap l ∷ []
cleanupMaps (cleanupWaiting _) = []
cleanupMaps (cleanupFinalize _ _) = []
cleanupMaps (cleanupCount _) = []
cleanupMaps (cleanupDone _) = []

cellMaps : MapCell → List ConnMap
cellMaps (full m) = m ∷ []
cellMaps (taken _) = []

retainedMaps : State → List ConnMap
retainedMaps s = cellMaps (mapCell (cm s)) ++
  concatMap (λ binding → admissionMaps (pc (proj₂ binding))) (admissions s) ++
  concatMap (λ binding → cleanupMaps (proj₂ binding)) (cleanups s)

-- This deliberately does not certify uniqueness, fresh supplies, lease ownership,
-- handler references or reachable continuations. SubsystemMapReferences derives
-- this predicate from its stronger preserved map/publication certificate.
CounterStateValid : State → Set
CounterStateValid s = All (CounterReferences (entries (cm s))) (retainedMaps s)

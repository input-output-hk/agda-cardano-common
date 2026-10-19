{-# OPTIONS --guardedness #-}

-- Project the stronger inductive certificate to the existing retained-map
-- counter-validity predicate, without changing that predicate.
module ConnectionManagement.Properties.MapReferencesCounters where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; concatMap)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (_,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Data.Maybe using (just)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Store using (Store)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Counters using (CounterReferences; count-total)
import ConnectionManagement.Properties.StateMapReferences as R
import ConnectionManagement.Properties.CounterState as C

-- Flatten the exact exhaustive continuation projections used by CounterState.
cell-references : ∀ heap cell → R.CellReferences heap cell → All (CounterReferences heap) (C.cellMaps cell)
cell-references heap (full m) valid = valid ∷ []
cell-references heap (taken _) valid = []
admission-references : ∀ heap p → R.AdmissionReferences heap p → All (CounterReferences heap) (C.admissionMaps p)
admission-references heap acquireMap valid = []
admission-references heap (count l) valid = valid ∷ []
admission-references heap (prepare l) valid = valid ∷ []
admission-references heap (selectEntry l p) valid = valid ∷ []
admission-references heap (forkHandler l p e) valid = proj₁ valid ∷ []
admission-references heap (publish l p e) valid = proj₁ valid ∷ []
admission-references heap (reject l reason) valid = valid ∷ []
admission-references heap (closeSocket reason) valid = []
admission-references heap (finished reason) valid = []
admission-references heap (countPublished p e) valid = []
admission-references heap (awaitHandshake p e) valid = []
admission-references heap (commitHandshake e result) valid = []
admission-references heap (countHandshake result) valid = []
admission-references heap (notifyInbound info) valid = []
admission-references heap (returnHandshake result) valid = []
admission-references heap (completedHandshake result) valid = []
admission-references heap impossibleHandshake valid = []
cleanup-references : ∀ heap p → R.CleanupReferences heap p → All (CounterReferences heap) (C.cleanupMaps p)
cleanup-references heap cleanupAcquire valid = []
cleanup-references heap (cleanupSelect l) valid = valid ∷ []
cleanup-references heap (cleanupClose l m tail) valid = proj₁ valid ∷ proj₂ valid ∷ []
cleanup-references heap (cleanupPublish l m tail) valid = proj₁ valid ∷ proj₂ valid ∷ []
cleanup-references heap (cleanupRestore l err) valid = valid ∷ []
cleanup-references heap (cleanupWaiting st) valid = []
cleanup-references heap (cleanupFinalize st outcome) valid = []
cleanup-references heap (cleanupCount outcome) valid = []
cleanup-references heap (cleanupDone outcome) valid = []

-- Combine certificates over every stored worker, including shadowed keys.
admission-store : ∀ heap (xs : Store WorkerId AdmissionWorker) → All (λ b → R.AdmissionValid heap (proj₂ b)) xs →
  All (CounterReferences heap) (concatMap (λ b → C.admissionMaps (pc (proj₂ b))) xs)
admission-store heap [] [] = []
admission-store heap ((w , a) ∷ xs) (valid ∷ rest) =
  ++⁺ (admission-references heap (pc a) valid) (admission-store heap xs rest)
cleanup-store : ∀ heap (xs : Store WorkerId CleanupPC) → All (λ b → R.CleanupReferences heap (proj₂ b)) xs →
  All (CounterReferences heap) (concatMap (λ b → C.cleanupMaps (proj₂ b)) xs)
cleanup-store heap [] [] = []
cleanup-store heap ((w , p) ∷ xs) (valid ∷ rest) =
  ++⁺ (cleanup-references heap p valid) (cleanup-store heap xs rest)

-- Preserve the original CounterStateValid type as the public consequence.
counter-state-valid : ∀ s → R.Valid s → C.CounterStateValid s
counter-state-valid s valid = ++⁺ (cell-references (entries (cm s)) (mapCell (cm s)) (proj₁ valid))
  (++⁺ (admission-store (entries (cm s)) (admissions s) (proj₁ (proj₂ valid)))
       (cleanup-store (entries (cm s)) (cleanups s) (proj₂ (proj₂ valid))))

-- A full current map has a successful structural counter traversal.
current-count-total : ∀ s m → mapCell (cm s) ≡ full m → R.Valid s →
  Σ ℕ (λ n → countIncoming (entries (cm s)) m ≡ just n)
current-count-total s m cell valid = count-total (entries (cm s)) m
  (subst (R.CellReferences (entries (cm s))) cell (proj₁ valid))

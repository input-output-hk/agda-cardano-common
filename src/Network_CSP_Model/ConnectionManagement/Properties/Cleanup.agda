{-# OPTIONS --guardedness #-}

-- Local cleanup guarantees. No fairness, eventual cleanup or full invariant.
module ConnectionManagement.Properties.Cleanup where

open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Rules.Cleanup
open import ConnectionManagement.Properties.Entries

purge-absent : ∀ k e m → lookupConnection k m ≡ nothing → purgeCaptured k e m ≡ m
purge-absent k e m absent rewrite absent = refl

purge-stale : ∀ k e current m → lookupConnection k m ≡ just current →
  e ≢ current → purgeCaptured k e m ≡ m
purge-stale k e current m found different rewrite found with e ≟ current
... | no _ = refl
... | yes same = ⊥-elim (different same)

selection-preserves-map-cell : ∀ w h l decision s →
  mapCell (cm (selectCleanup w h l decision s)) ≡ mapCell (cm s)
selection-preserves-map-cell w h l terminateAndPurge s = refl
selection-preserves-map-cell w h l purgeOnly s = refl
selection-preserves-map-cell w h l (waitBeforePurge st) s = refl

selection-preserves-references : ∀ w h l decision s m →
  MapReferences (entries (cm s)) m →
  MapReferences (entries (cm (selectCleanup w h l decision s))) m
selection-preserves-references w h l terminateAndPurge s m valid =
  heap-update-preserves-map-references (handlerEntry h) (terminated nothing) (entries (cm s)) m valid
selection-preserves-references w h l purgeOnly s m valid = valid
selection-preserves-references w h l (waitBeforePurge st) s m valid = valid

-- The finalizer cannot commit even its entry write while the map is held.
finalizer-waits-atomically : ∀ w h captured outcome owner heap n ads hs ss ps next rs info cs →
  stepWorker w h (cleanupFinalize captured outcome) finishTimeWait
    (state (cmStore (taken owner) heap n) ads hs ss ps next rs info cs) ≡ nothing
finalizer-waits-atomically w h captured outcome owner heap n ads hs ss ps next rs info cs = refl

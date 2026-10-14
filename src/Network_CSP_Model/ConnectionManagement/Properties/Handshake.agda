{-# OPTIONS --guardedness #-}

-- Local safety for the successful-result transaction, including its exception
-- and disconnected outcomes. No reachability or full-machine invariant claim.
module ConnectionManagement.Properties.Handshake where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.Handshake
open import ConnectionManagement.Properties.Entries

success-preserves-map : ∀ w a e h f decision s →
  mapCell (cm (applySuccess w a e h f decision s)) ≡ mapCell (cm s)
success-preserves-map w a e h f (update st p) s = refl
success-preserves-map w a e h f (retain p) s = refl
success-preserves-map w a e h f (disconnect r) s = refl
success-preserves-map w a e h f impossible s = refl

-- The map can be the published map or a worker's saved map. Heap writes preserve
-- every previously valid reference, even if this caller's entry is now unmapped.
success-preserves-references : ∀ w a e h f decision s m →
  MapReferences (entries (cm s)) m →
  MapReferences (entries (cm (applySuccess w a e h f decision s))) m
success-preserves-references w a e h f (update st p) s m valid =
  heap-update-preserves-map-references e st (entries (cm s)) m valid
success-preserves-references w a e h f (retain p) s m valid = valid
success-preserves-references w a e h f (disconnect r) s m valid = valid
success-preserves-references w a e h f impossible s m valid = valid

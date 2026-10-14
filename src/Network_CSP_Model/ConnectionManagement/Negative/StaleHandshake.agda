{-# OPTIONS --guardedness #-}

-- Negative control for a modeling shortcut, not a source-bug witness. Removing
-- by connection key alone incorrectly purges the replacement incarnation.
module ConnectionManagement.Negative.StaleHandshake where

open import Data.Maybe using (Maybe; just; nothing; map)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import ConnectionManagement.State
open import ConnectionManagement.Scenarios.Admission using (key₀)
open import ConnectionManagement.Scenarios.Handshake using
  (resume; bind; replaceBinding; staleQuery)
open import ConnectionManagement.Rules.Handshake using (readResult)
open import Data.List using ([]; _∷_)

-- Deliberately bad: skip the captured/current entry identity comparison.
keyOnlyPurge : State → Maybe State
keyOnlyPurge s with mapCell (cm s)
... | taken _ = nothing
... | full m = just (record s { cm = record (cm s)
    { mapCell = full (deleteConnection key₀ m) } })

badQuery : Maybe State
badQuery = bind (map replaceBinding (resume query responderMode (readResult ∷ []))) keyOnlyPurge

identity-check-matters : map (λ s → mapCell (cm s)) staleQuery ≢
  map (λ s → mapCell (cm s)) badQuery
identity-check-matters ()

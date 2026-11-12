{-# OPTIONS --guardedness #-}

-- G1 local FirstToFinish/LastToFinish result-cell controls. No protocol body
-- or physical Async exit is inferred from one of these STM observations.
module ConnectionManagement.Negative.PrimitiveResults where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (errorId)
open import ConnectionManagement.IGTypes using (hot; onDemand; protocol; clean; errored)
import ConnectionManagement.Rules.PeerActions as P

-- An unordered list must still select the lowest protocol number ready.
low high pending retired : P.ProtocolRun
low = P.protocolRun (protocol 1 hot onDemand) (P.returned clean) P.running
high = P.protocolRun (protocol 2 hot onDemand) (P.returned (errored (errorId 2))) P.running
pending = P.protocolRun (protocol 1 hot onDemand) P.running P.running
retired = record low { published = P.notRunning clean }
first-enabled : P.first hot (high ∷ low ∷ []) ≡ just clean
first-enabled = refl
first-empty-refused : P.first hot [] ≡ nothing
first-empty-refused = refl
first-retired-prefix-refused : P.first hot (high ∷ retired ∷ []) ≡ nothing
first-retired-prefix-refused = refl
all-empty-enabled : P.all hot [] ≡ just clean
all-empty-enabled = refl
all-returned-enabled : P.all hot (retired ∷ low ∷ []) ≡ just clean
all-returned-enabled = refl
all-error-enabled : P.all hot (low ∷ high ∷ []) ≡ just (errored (errorId 2))
all-error-enabled = refl
all-pending-refused : P.all hot (low ∷ pending ∷ []) ≡ nothing
all-pending-refused = refl

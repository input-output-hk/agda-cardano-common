{-# OPTIONS --guardedness #-}

-- Small generic adapters retain the real successful PS/K guards.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesLifts
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module D = Cancellation isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- A governor component proof passes through the actual PSA permission check.
governor-lift : ∀ a s {t} →
  (∀ {g′} → GP.step a (PS.governor s) ≡ just g′ → D.Held s → D.Held (record s { governor = g′ })) →
  (∀ after → PS.noteGovernor a s after ≡ after) → PS.step (PS.run a) s ≡ just t → D.Held s → D.Held t
governor-lift a s preserves note stepped held with PS.governorAllowed a s
... | false = case stepped of λ ()
... | true with GP.step a (PS.governor s) in advanced
...   | nothing = case stepped of λ ()
...   | just g′ = case just-injective stepped of λ { refl → subst D.Held
  (sym (note (record s { governor = g′ }))) (preserves refl held) }

-- The shared K writer reassembles exactly the PS source and observed context.
peer-lift : ∀ a → (∀ p {q} → PS.step a p ≡ just q → D.Held p → D.Held q) →
  ∀ s {t} → K.step (K.peerStep a) s ≡ just t → R.Reach s → R.Reach t
peer-lift a preserves s stepped held with K.peerOpen s ∧ K.peerAllowed a s
... | false = case stepped of λ ()
... | true with PS.step a (K.peers s) in advanced
...   | nothing = case stepped of λ ()
...   | just p = case just-injective stepped of λ { refl → preserves (K.peers s) advanced held }

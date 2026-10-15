{-# OPTIONS --guardedness #-}

-- Preserve existing immutable lookups while allowing fresh table growth.
module ConnectionManagement.Properties.StateRetention where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (Present)
import ConnectionManagement.Properties.CleanupRetention as Cleanup

record Retains (s s′ : State) : Set where
  field
    handlersRetained : ∀ w h → lookup w (handlers s) ≡ just h → lookup w (handlers s′) ≡ just h
    resultsRetained : ∀ p r → lookup p (handshakeResults s) ≡ just r → lookup p (handshakeResults s′) ≡ just r
    entriesRetained : ∀ e → Present e (entries (cm s)) → Present e (entries (cm s′))
    socketsRetained : ∀ sock → Present sock (sockets s) → Present sock (sockets s′)
open Retains public

-- Embed the earlier exact-store guarantee without changing its type.
from-cleanup : ∀ {s s′} → Cleanup.Retains s s′ → Retains s s′
handlersRetained (from-cleanup eff) w h found = trans (cong (lookup w) (Cleanup.handlersSame eff)) found
resultsRetained (from-cleanup eff) p r found = trans (cong (lookup p) (Cleanup.resultsSame eff)) found
entriesRetained (from-cleanup eff) = Cleanup.entriesRetained eff
socketsRetained (from-cleanup eff) = Cleanup.socketsRetained eff

-- Exact immutable stores are a sufficient special case.
reframe : ∀ {s} s′ → handlers s′ ≡ handlers s → handshakeResults s′ ≡ handshakeResults s →
  (∀ e → Present e (entries (cm s)) → Present e (entries (cm s′))) →
  (∀ sock → Present sock (sockets s) → Present sock (sockets s′)) → Retains s s′
reframe s′ hs rs ep sp = from-cleanup (Cleanup.retains hs rs ep sp)

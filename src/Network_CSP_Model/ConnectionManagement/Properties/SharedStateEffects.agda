{-# OPTIONS --guardedness #-}

-- Transparent store effects ignore unrelated state fields while retaining all
-- original immutable lookups and mutable resource identities.
module ConnectionManagement.Properties.SharedStateEffects where

open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.IGTableRetention using (fresh-lookup)
import ConnectionManagement.Properties.StateRetention as R
import ConnectionManagement.Properties.CleanupRetention as Cleanup

-- Result/handler values remain exact; entry/socket values may change.
Effects : State → State → Set
Effects s s′ =
  (∀ w h → lookup w (handlers s) ≡ just h → lookup w (handlers s′) ≡ just h) ×
  (∀ p r → lookup p (handshakeResults s) ≡ just r → lookup p (handshakeResults s′) ≡ just r) ×
  (∀ e → Present e (entries (cm s)) → Present e (entries (cm s′))) ×
  (∀ sock → Present sock (sockets s) → Present sock (sockets s′))

-- Interoperate with the existing inbound retention relation.
to-retains : ∀ {s s′} → Effects s s′ → R.Retains s s′
to-retains (hs , rs , es , ss) = record
  { handlersRetained = hs; resultsRetained = rs; entriesRetained = es; socketsRetained = ss }
from-retains : ∀ {s s′} → R.Retains s s′ → Effects s s′
from-retains eff = R.handlersRetained eff , R.resultsRetained eff , R.entriesRetained eff , R.socketsRetained eff
from-cleanup : ∀ {s s′} → Cleanup.Retains s s′ → Effects s s′
from-cleanup eff = from-retains (R.from-cleanup eff)

-- Identity effects allow arbitrary changes to unobserved fields.
identity : ∀ s → Effects s s
identity s = (λ w h p → p) , (λ q r p → p) , (λ e p → p) , (λ sock p → p)

-- A single entry or socket write retains every old identity.
entry-write : ∀ e st s → Effects s
  (record s { cm = record (cm s) { entries = put e st (entries (cm s)) } })
entry-write e st s = (λ w h p → p) , (λ q r p → p) ,
  (λ q → put-preserves-present e q st (entries (cm s))) , (λ sock p → p)
socket-write : ∀ sock owner s → Effects s (record s { sockets = put sock owner (sockets s) })
socket-write sock owner s = (λ w h p → p) , (λ q r p → p) , (λ e p → p) ,
  (λ q → put-preserves-present sock q owner (sockets s))

-- The absent-child guard preserves complete existing handler lookups.
fork-write : ∀ child descriptor s → lookup child (handlers s) ≡ nothing → Effects s
  (record s { handlers = put child descriptor (handlers s)
            ; sockets = put (handlerSocket descriptor) (handling child) (sockets s) })
fork-write child descriptor s absent =
  (λ q old → fresh-lookup child q descriptor old (handlers s) absent) ,
  (λ q r p → p) , (λ e p → p) ,
  (λ q → put-preserves-present (handlerSocket descriptor) q (handling child) (sockets s))

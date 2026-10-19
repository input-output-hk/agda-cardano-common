{-# OPTIONS --guardedness #-}

-- Fix the original handler descriptor while transporting its resource facts.
module ConnectionManagement.Properties.HandlerResourceFacts where

open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.HandlerResources using (Resources; original; found; entryExists; socketExists)
open import ConnectionManagement.Properties.IGTableRetention using (fresh-lookup)
import ConnectionManagement.Properties.CleanupRetention as Cleanup

-- This transparent product observes only the three relevant stores.
Facts : WorkerId → HandlerStart → State → Set
Facts w h s = lookup w (handlers s) ≡ just h ×
  Present (handlerEntry h) (entries (cm s)) × Present (handlerSocket h) (sockets s)

from-resources : ∀ {w s} (r : Resources w s) → Facts w (original r) s
from-resources r = found r , entryExists r , socketExists r

to-resources : ∀ {w h s} → Facts w h s → Resources w s
to-resources {h = h} (found , allocated , storedSocket) = record
  { original = h; found = found; entryExists = allocated; socketExists = storedSocket }

-- Writes change resource values while preserving their stored identities.
entry-write : ∀ {w h} e st s → Facts w h s →
  Facts w h (record s { cm = record (cm s) { entries = put e st (entries (cm s)) } })
entry-write {h = h} e st s (found , allocated , storedSocket) = found ,
  put-preserves-present e (handlerEntry h) st (entries (cm s)) allocated , storedSocket
socket-write : ∀ {w h} sock owner s → Facts w h s →
  Facts w h (record s { sockets = put sock owner (sockets s) })
socket-write {h = h} sock owner s (found , allocated , storedSocket) = found , allocated ,
  put-preserves-present sock (handlerSocket h) owner (sockets s) storedSocket

-- Freshness guards preserve the complete original handler lookup, even when
-- another actor writes an existing storedSocket's owner field.
fork-write : ∀ {w h} child descriptor s → lookup child (handlers s) ≡ nothing → Facts w h s →
  Facts w h (record s { handlers = put child descriptor (handlers s)
                    ; sockets = put (handlerSocket descriptor) (handling child) (sockets s) })
fork-write {w} {h} child descriptor s absent (found , allocated , storedSocket) =
  fresh-lookup child w descriptor h (handlers s) absent found , allocated ,
  put-preserves-present (handlerSocket descriptor) (handlerSocket h) (handling child) (sockets s) storedSocket

-- Existing atomic pruning/cleanup effects transport the same facts.
cleanup-retained : ∀ {w h s s′} → Cleanup.Retains s s′ → Facts w h s → Facts w h s′
cleanup-retained {w} {h} eff (found , allocated , storedSocket) =
  trans
    (cong (lookup w) (Cleanup.handlersSame eff)) found ,
  Cleanup.entriesRetained eff (handlerEntry h) allocated , Cleanup.socketsRetained eff (handlerSocket h) storedSocket

import ConnectionManagement.Properties.StateRetention as StateRetention

-- The inbound dispatcher permits fresh handler/result table growth.
state-retained : ∀ {w h s s′} → StateRetention.Retains s s′ → Facts w h s → Facts w h s′
state-retained {w} {h} eff (found , allocated , storedSocket) =
  StateRetention.handlersRetained eff w h found ,
  StateRetention.entriesRetained eff (handlerEntry h) allocated ,
  StateRetention.socketsRetained eff (handlerSocket h) storedSocket

{-# OPTIONS --guardedness #-}

-- Successful inbound selection allocates the entry later installed in the map.
module ConnectionManagement.Properties.AdmissionAllocation where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (Present; lookup-put)
import ConnectionManagement.Rules.CM as CM

-- Fresh selection inserts the returned identity into the heap before returning.
fresh-allocated : ∀ r c {e c′} → CM.freshInbound r c ≡ just (CM.selected e c′) → Present e (entries c′)
fresh-allocated r c eq with lookup (ident (nextEntry c)) (entries c)
... | just _ = case eq of λ ()
... | nothing with just-injective eq
...   | refl = unnegotiated inbound (key r) (child r) ,
  lookup-put (ident (nextEntry c)) (unnegotiated inbound (key r) (child r)) (entries c)

-- Successful reuse writes its existing identity; terminal replacement is fresh.
existing-allocated : ∀ e st r c {e′ c′} → CM.existingInbound e st r c ≡ just (CM.selected e′ c′) → Present e′ (entries c′)
existing-allocated e reservedOutbound r c eq with just-injective eq
... | refl = unnegotiated inbound (key r) (child r) , lookup-put e (unnegotiated inbound (key r) (child r)) (entries c)
existing-allocated e (unnegotiated _ _ _) r c eq with just-injective eq
... | refl = unnegotiated inbound (key r) (child r) , lookup-put e (unnegotiated inbound (key r) (child r)) (entries c)
existing-allocated e (terminating _ _ _) r c eq = fresh-allocated r c eq
existing-allocated e (terminated _) r c eq = fresh-allocated r c eq
existing-allocated e (outboundUni _ _ _) r c ()
existing-allocated e (outboundDup _ _ _ _) r c ()
existing-allocated e (outboundIdle _ _ _ _) r c ()
existing-allocated e (inboundIdle _ _ _ _) r c ()
existing-allocated e (inboundActive _ _ _ _) r c ()
existing-allocated e (duplexActive _ _ _) r c ()

-- The actual selection primitive discharges the future publication obligation.
selected-allocated : ∀ l r c {e c′} → CM.selectInbound l r c ≡ just (CM.selected e c′) → Present e (entries c′)
selected-allocated l r c eq with mapCell c
... | full _ = case eq of λ ()
... | taken w with owner l ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookupConnection (key r) (savedMap l)
...     | nothing = fresh-allocated r c eq
...     | just e with lookup e (entries c)
...       | nothing = case eq of λ ()
...       | just st = existing-allocated e st r c eq

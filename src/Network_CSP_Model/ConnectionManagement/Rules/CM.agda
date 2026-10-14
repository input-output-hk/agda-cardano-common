{-# OPTIONS --guardedness #-}

-- Core.hs:801-885 and 2366-2399 at the pinned revision. These are primitive
-- operations, not a complete CM dispatcher or an exception-delivery semantics.
module ConnectionManagement.Rules.CM where

open import Data.Nat using (suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State

-- Taking the TMVar captures its map; the entry heap is not removed.
takeMap : WorkerId → CMStore → Maybe (Lease × CMStore)
takeMap w c with mapCell c
... | taken _ = nothing
... | full m = just (lease w m , record c { mapCell = taken w })

-- Only the owner can complete the IO helper. This does not restore the heap.
putMap : Lease → ConnMap → CMStore → Maybe CMStore
putMap l m c with mapCell c
... | full _ = nothing
... | taken w with owner l ≟ w
...   | no _ = nothing
...   | yes _ = just (record c { mapCell = full m })

restoreMap : Lease → CMStore → Maybe CMStore
restoreMap l = putMap l (savedMap l)

-- A previously captured TVar can still be written while the map is taken.
-- Caller-specific guards belong to the source rule invoking this primitive.
writeCaptured : EntryId → ConnectionState → CMStore → Maybe CMStore
writeCaptured e st c with lookup e (entries c)
... | nothing = nothing
... | just _ = just (record c { entries = put e st (entries c) })

-- Denial is an exception outcome, not a disabled transaction.
data Selection : Set where
  selected : EntryId → CMStore → Selection
  denied : Selection

-- Allocation is fresh; supply exhaustion is not part of semantic execution.
freshInbound : Admission → CMStore → Maybe Selection
freshInbound r c with lookup (ident (nextEntry c)) (entries c)
... | just _ = nothing -- malformed supply; not a source retry
... | nothing = just (selected (ident (nextEntry c))
    (record c { entries = put (ident (nextEntry c))
                       (unnegotiated inbound (key r) (child r)) (entries c)
              ; nextEntry = suc (nextEntry c) }))

-- Reserved/unnegotiated overwrite retains the mutable entry identity.
existingInbound : EntryId → ConnectionState → Admission → CMStore → Maybe Selection
existingInbound e reservedOutbound r c = just (selected e
  (record c { entries = put e (unnegotiated inbound (key r) (child r)) (entries c) }))
existingInbound e (unnegotiated _ _ _) r c = just (selected e
  (record c { entries = put e (unnegotiated inbound (key r) (child r)) (entries c) }))
existingInbound e (terminating _ _ _) r c = freshInbound r c
existingInbound e (terminated _) r c = freshInbound r c
existingInbound e _ r c = just denied

-- One entry-selection STM commit while the caller owns the enclosing map lock.
selectOwned : Lease → Admission → CMStore → Maybe Selection
selectOwned l r c with lookupConnection (key r) (savedMap l)
... | nothing = freshInbound r c
... | just e with lookup e (entries c)
...   | nothing = nothing -- malformed dangling reference
...   | just st = existingInbound e st r c

selectInbound : Lease → Admission → CMStore → Maybe Selection
selectInbound l r c with mapCell c
... | full _ = nothing
... | taken w with owner l ≟ w
...   | no _ = nothing
...   | yes _ = selectOwned l r c

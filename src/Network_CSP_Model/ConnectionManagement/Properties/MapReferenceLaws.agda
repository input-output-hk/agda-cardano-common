{-# OPTIONS --guardedness #-}

-- Structural map-reference laws cover shadowed association bindings too.
module ConnectionManagement.Properties.MapReferenceLaws where

open import Data.Bool using (true; false; T?)
open import Data.List using ([]; _∷_; filterᵇ)
open import Data.List.Relation.Unary.All using ([]; _∷_; map)
open import Data.List.Relation.Unary.All.Properties using (filter⁺)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.Entries using (Present)
open import ConnectionManagement.Properties.Counters using (InnerReferences; CounterReferences; lookup-all)
open import ConnectionManagement.Properties.Stores using (put-values; delete-values)
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.Cleanup as Cleanup

-- Existing pointers remain valid under heap retention, irrespective of values.
map-retained : ∀ heap heap′ m → (∀ e → Present e heap → Present e heap′) →
  CounterReferences heap m → CounterReferences heap′ m
map-retained heap heap′ m retains = map (map (λ { {x = local , e} → retains e }))

-- Insertion needs a certificate for the identity being installed.
insert-references : ∀ heap remote local e m → Present e heap →
  CounterReferences heap m → CounterReferences heap (insertLocal remote local e m)
insert-references heap remote local e m present valid with lookup remote m in found
... | nothing = put-values (InnerReferences heap) remote ((local , e) ∷ []) m (present ∷ []) valid
... | just inner = put-values (InnerReferences heap) remote (put local e inner) m
  (put-values (λ e → Present e heap) local e inner present
    (lookup-all (InnerReferences heap) remote m valid found)) valid

-- Exact-key deletion and dropping an empty bucket introduce no references.
delete-references : ∀ heap k m → CounterReferences heap m →
  CounterReferences heap (deleteConnection k m)
delete-references heap k m valid with lookup (remote k) m in found
... | nothing = valid
... | just inner with delete (knownLocal (local k)) inner in deleted
...   | [] = delete-values (InnerReferences heap) (remote k) m valid
...   | x ∷ xs = put-values (InnerReferences heap) (remote k) (x ∷ xs) m
  (subst (InnerReferences heap) deleted
    (delete-values (λ e → Present e heap) (knownLocal (local k)) inner
      (lookup-all (InnerReferences heap) (remote k) m valid found))) valid

-- Moving the reservation reuses its existing pointer certificate.
update-local-references : ∀ heap k m → CounterReferences heap m →
  CounterReferences heap (proj₂ (A.updateLocal k m))
update-local-references heap k m valid with lookup (remote k) m in found
... | nothing = valid
... | just inner with lookup unknownLocal inner in reserved
...   | nothing = valid
...   | just e with lookup (knownLocal (local k)) inner
...     | just _ = put-values (InnerReferences heap) (remote k) (delete unknownLocal inner) m
  (delete-values (λ e → Present e heap) unknownLocal inner
    (lookup-all (InnerReferences heap) (remote k) m valid found)) valid
...     | nothing = put-values (InnerReferences heap) (remote k) (put (knownLocal (local k)) e (delete unknownLocal inner)) m
  (put-values (λ e → Present e heap) (knownLocal (local k)) e (delete unknownLocal inner)
    (lookup-all (λ e → Present e heap) unknownLocal inner
      (lookup-all (InnerReferences heap) (remote k) m valid found) reserved)
    (delete-values (λ e → Present e heap) unknownLocal inner
      (lookup-all (InnerReferences heap) (remote k) m valid found))) valid

-- Alias filtering preserves references in every retained binding.
remove-aliases-references : ∀ heap p e m → CounterReferences heap m →
  CounterReferences heap (A.removeAliases p e m)
remove-aliases-references heap p e m valid with lookup p m in found
... | nothing = valid
... | just inner with filterᵇ (λ pair → A.differentEntry (proj₂ pair) e) inner in filtered
...   | [] = delete-values (InnerReferences heap) p m valid
...   | x ∷ xs = put-values (InnerReferences heap) p (x ∷ xs) m
  (subst (InnerReferences heap) filtered
    (filter⁺ (λ pair → T? (A.differentEntry (proj₂ pair) e))
      (lookup-all (InnerReferences heap) p m valid found))) valid

-- Cleanup's identity guard selects either no deletion or the exact-key law.
purge-references : ∀ heap k e m → CounterReferences heap m →
  CounterReferences heap (Cleanup.purgeCaptured k e m)
purge-references heap k e m valid with lookupConnection k m
... | nothing = valid
... | just current with e ≟ current
...   | no _ = valid
...   | yes _ = delete-references heap k m valid

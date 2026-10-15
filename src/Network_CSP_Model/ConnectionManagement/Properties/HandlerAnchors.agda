{-# OPTIONS --guardedness #-}

-- Immutable handle references and retained mux keys; dynamic mux state is free
-- to change. This relation does not require a current CM or IG registration.
module ConnectionManagement.Properties.HandlerAnchors where

open import Data.Product using (Σ; _×_; _,_)
open import Data.Maybe using (just)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M

record Anchors (before after : IG.Runtime) : Set where
  field
    handlesSame : IG.handles (IG.execution after) ≡ IG.handles (IG.execution before)
    muxesRetained : ∀ mid m → lookup mid (IG.muxes (IG.execution before)) ≡ just m →
      Σ M.Mux (λ m′ → lookup mid (IG.muxes (IG.execution after)) ≡ just m′ × M.key m′ ≡ M.key m)
open Anchors public

anchors-refl : ∀ ig → Anchors ig ig
handlesSame (anchors-refl ig) = refl
muxesRetained (anchors-refl ig) mid m found = m , found , refl

-- Changing status, protocol jobs or callbacks preserves the existing mux key.
setMux-preserves : ∀ mid old new ig → lookup mid (IG.muxes (IG.execution ig)) ≡ just old →
  M.key new ≡ M.key old → Anchors ig (IG.setMux mid new ig)
handlesSame (setMux-preserves mid old new ig found same) = refl
muxesRetained (setMux-preserves mid old new ig found same) q m query with q ≟ mid
... | yes refl = new , lookup-put mid new (IG.muxes (IG.execution ig)) ,
  trans same (cong M.key (just-injective (trans (sym found) query)))
... | no neq = m , trans (lookup-put-other mid q new (IG.muxes (IG.execution ig)) neq) query , refl

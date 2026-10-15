{-# OPTIONS --guardedness #-}

-- Table growth retains old handles and mux identities; dynamic mux state may change.
module ConnectionManagement.Properties.IGTableRetention where

open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.Properties.HandlerAnchors as A
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M

record Retains (before after : IG.Runtime) : Set where
  field
    handlesRetained : ∀ hid hd → lookup hid (IG.handles (IG.execution before)) ≡ just hd →
      lookup hid (IG.handles (IG.execution after)) ≡ just hd
    muxesRetained : ∀ mid m → lookup mid (IG.muxes (IG.execution before)) ≡ just m →
      Σ M.Mux (λ m′ → lookup mid (IG.muxes (IG.execution after)) ≡ just m′ × M.key m′ ≡ M.key m)
open Retains public

-- Embed the stronger equality relation without weakening its existing API.
from-anchors : ∀ {ig ig′} → A.Anchors ig ig′ → Retains ig ig′
handlesRetained (from-anchors a) hid hd found = trans (cong (lookup hid) (A.handlesSame a)) found
muxesRetained (from-anchors a) = A.muxesRetained a

-- Fresh allocation preserves every old lookup, without requiring unique stores.
fresh-lookup : ∀ {K V} ⦃ _ : DecEq K ⦄ (k q : K) (v old : V) xs →
  lookup k xs ≡ nothing → lookup q xs ≡ just old → lookup q (put k v xs) ≡ just old
fresh-lookup k q v old xs absent found with q ≟ k
... | yes refl = case trans (sym absent) found of λ ()
... | no neq = trans (lookup-put-other k q v xs neq) found

-- Both absent-key premises come from the executable installation guards.
extend-retains : ∀ hid hd mid m ig →
  lookup hid (IG.handles (IG.execution ig)) ≡ nothing →
  lookup mid (IG.muxes (IG.execution ig)) ≡ nothing →
  Retains ig (record ig { execution = record (IG.execution ig)
    { handles = put hid hd (IG.handles (IG.execution ig)); muxes = put mid m (IG.muxes (IG.execution ig)) } })
handlesRetained (extend-retains hid hd mid m ig noHandle noMux) q old found =
  fresh-lookup hid q hd old (IG.handles (IG.execution ig)) noHandle found
muxesRetained (extend-retains hid hd mid m ig noHandle noMux) q old found =
  old , fresh-lookup mid q m old (IG.muxes (IG.execution ig)) noMux found , refl

-- Replacing governor membership/control does not change either reference table.
control-retains : ∀ old n pc ig → Retains ig (IG.runtimeState old n pc (IG.execution ig))
handlesRetained (control-retains old n pc ig) hid hd found = found
muxesRetained (control-retains old n pc ig) mid m found = m , found , refl

{-# OPTIONS --guardedness #-}

-- Immutable captured mux identity. This theorem says nothing about whether the
-- captured mux exists or whether two workers share it; validity is separate.
module ConnectionManagement.Properties.HandlerCapture where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State hiding (capturedMux)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote

-- Each prior lookup still resolves to a frame with the same captured mux.
Retains : L.Runtime → L.Runtime → Set
Retains before after = ∀ w f → lookup w before ≡ just f →
  Σ L.Frame (λ g → lookup w after ≡ just g × L.capturedMux g ≡ L.capturedMux f)
retains-refl : ∀ rt → Retains rt rt
retains-refl rt w f found = f , found , refl
retains-trans : ∀ {r₀ r₁ r₂} → Retains r₀ r₁ → Retains r₁ r₂ → Retains r₀ r₂
retains-trans left right w f found with left w f found
... | g , fg , same with right w g fg
...   | h , gh , same′ = h , gh , trans same′ same

open import ConnectionManagement.Properties.Stores using (lookup-put-other) public

phase-retains : ∀ w f p rt → lookup w rt ≡ just f → Retains rt (L.setPhase w f p rt)
phase-retains w f p rt owned q old found with q ≟ w
... | yes refl = record f { phase = p } , lookup-put w (record f { phase = p }) rt ,
  cong L.capturedMux (just-injective (trans (sym owned) found))
... | no neq = old , trans (lookup-put-other w q (record f { phase = p }) rt neq) found , refl
fresh-retains : ∀ w f rt → lookup w rt ≡ nothing → Retains rt (put w f rt)
fresh-retains w f rt absent q old found with q ≟ w
... | yes refl = case trans (sym absent) found of λ ()
... | no neq = old , trans (lookup-put-other w q f rt neq) found , refl

-- Shared rule analysis also carries attachment's no-shared-mux guard.
import ConnectionManagement.Properties.HandlerEvolution as E

evolution-retains : ∀ {rt rt′} → E.Evolution rt rt′ → Retains rt rt′
evolution-retains {rt} E.unchanged = retains-refl rt
evolution-retains (E.attached w f rt absent unused) = fresh-retains w f rt absent
evolution-retains (E.phaseChanged w f p rt owned) = phase-retains w f p rt owned
attach-retains : ∀ w err rt ig s {rt′ ig′} →
  L.attachMux w err rt ig s ≡ just (rt′ , ig′) → Retains rt rt′
attach-retains w err rt ig s eq = evolution-retains (E.attach-evolves w err rt ig s eq)
step-retains : ∀ w a rt ig s {rt′ ig′} →
  L.step w a rt ig s ≡ just (rt′ , ig′) → Retains rt rt′
step-retains w a rt ig s eq = evolution-retains (E.step-evolves w a rt ig s eq)
delivery-retains : ∀ w rt → Retains rt (L.noteDelivery w rt)
delivery-retains w rt = evolution-retains (E.delivery-evolves w rt)
exit-retains : ∀ w rt → Retains rt (L.noteExit w rt)
exit-retains w rt = evolution-retains (E.exit-evolves w rt)
release-retains : ∀ a rt → Retains rt (L.noteRelease a rt)
release-retains a rt = evolution-retains (E.release-evolves a rt)
remote-retains : ∀ a rt → Retains rt (L.noteRemote a rt)
remote-retains a rt = evolution-retains (E.remote-evolves a rt)

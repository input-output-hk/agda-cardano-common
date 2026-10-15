{-# OPTIONS --guardedness #-}

-- Extend caller interference with mux execution, handler exit and all cleanup.
-- This preserves reference evidence, not publication or attachment readiness.
module ConnectionManagement.Properties.HandlerRuntimeInterference where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present)
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerEstablishment using (Prepared)
open import ConnectionManagement.Properties.HandlerReferences using (Chain; anchors-preserve-chain)
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors; anchors-refl; handlesSame; muxesRetained)
import ConnectionManagement.Properties.HandlerInterference as Caller
import ConnectionManagement.Properties.HandlerConsumerEffects as Effects
import ConnectionManagement.Properties.CleanupRetention as Cleanup
import ConnectionManagement.Properties.MuxRetention as Mux
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L

resources-retained : ∀ {w s s′} → Cleanup.Retains s s′ → Resources w s → Resources w s′
resources-retained eff r = record
  { original = original r; found = trans (cong (lookup _) (Cleanup.handlersSame eff)) (found r)
  ; entryExists = Cleanup.entriesRetained eff _ (entryExists r)
  ; socketExists = Cleanup.socketsRetained eff _ (socketExists r) }

prepared-retained : ∀ {w hid mid s s′ ig ig′} → Cleanup.Retains s s′ → Anchors ig ig′ →
  Prepared w hid mid s ig → Prepared w hid mid s′ ig′
prepared-retained {hid = hid} {mid} eff anchors p with muxesRetained anchors mid (Prepared.mx p) (Prepared.muxFound p)
... | m′ , muxFound , same = record
  { resources = resources-retained eff (Prepared.resources p)
  ; hd = Prepared.hd p; mx = m′
  ; handleFound = trans (cong (lookup hid) (handlesSame anchors)) (Prepared.handleFound p)
  ; handleMux = Prepared.handleMux p; muxFound = muxFound
  ; keyMatches = trans same (Prepared.keyMatches p) }

data Covered : Action → Set where
  caller : ∀ {a} → Caller.Covered a → Covered a
  mux : ∀ {a} → Mux.CoveredMux a → Covered (igStep a)
  cleanup : ∀ {w a} → Covered (cleanupStep w a)
  exit : ∀ {w} → Covered (handlerExit w)

-- Beginning cleanup only changes cleanup control state.
exit-retains : ∀ w s {s′} → C.beginCleanupBoundary w s ≡ just s′ → Cleanup.Retains s s′
exit-retains w s eq with lookup w (handlers s) | lookup w (cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just _ | nothing with just-injective eq
...   | refl = Cleanup.retains refl refl (λ _ p → p) (λ _ p → p)

step-effects : ∀ a → Covered a → ∀ c {c′} → advance a c ≡ just c′ →
  Cleanup.Retains (world c) (world c′) × Anchors (inboundGovernor c) (inboundGovernor c′)
step-effects a (caller covered) c eq with Caller.step-effect a covered c eq
... | eff , refl = Cleanup.retains (Effects.handlersSame eff) (Effects.resultsSame eff)
  (Effects.entriesRetained eff) (λ sock p → subst (Present sock) (sym (Effects.socketsSame eff)) p) , anchors-refl _
step-effects .(igStep a) (mux {a} covered) c eq with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig′ , queue′) with just-injective eq
...     | refl = Cleanup.retains refl refl (λ _ p → p) (λ _ p → p) ,
  Mux.mode-anchors (responder c) a covered (inboundGovernor c) (inboundInfo (world c)) stepped
step-effects .(cleanupStep w a) (cleanup {w} {a}) c eq with C.stepCleanup w a (world c) in stepped
... | nothing = case eq of λ ()
... | just s′ with just-injective eq
...   | refl = Cleanup.cleanup-retains w a (world c) stepped , anchors-refl _
step-effects .(handlerExit w) (exit {w}) c eq with L.mayExit w (handlerLifecycles c)
... | false = case eq of λ ()
... | true with C.beginCleanupBoundary w (world c) in entered
...   | nothing = case eq of λ ()
...   | just s′ with just-injective eq
...     | refl = exit-retains w (world c) entered , anchors-refl _

resources-step : ∀ a → Covered a → ∀ c {c′ w} → advance a c ≡ just c′ →
  Resources w (world c) → Resources w (world c′)
resources-step a covered c eq = resources-retained (proj₁ (step-effects a covered c eq))
prepared-step : ∀ a → Covered a → ∀ c {c′ w hid mid} → advance a c ≡ just c′ →
  Prepared w hid mid (world c) (inboundGovernor c) → Prepared w hid mid (world c′) (inboundGovernor c′)
prepared-step a covered c eq p with step-effects a covered c eq
... | eff , anchors = prepared-retained eff anchors p
chain-step : ∀ a → Covered a → ∀ c {c′ w mid} → advance a c ≡ just c′ →
  Chain w mid (world c) (inboundGovernor c) → Chain w mid (world c′) (inboundGovernor c′)
chain-step a covered c eq ch with step-effects a covered c eq
... | eff , anchors = anchors-preserve-chain anchors (Cleanup.retains-chain eff ch)

data Interference : List Action → Set where
  empty : Interference []
  more : ∀ {a as} → Covered a → Interference as → Interference (a ∷ as)

include-caller : ∀ {as} → Caller.Interference as → Interference as
include-caller Caller.empty = empty
include-caller (Caller.more covered rest) = more (caller covered) (include-caller rest)

resources-exec : ∀ {c as c′ w} → Interference as → Executes c as c′ → Resources w (world c) → Resources w (world c′)
resources-exec empty done r = r
resources-exec (more {a} covered rest) (next {c = c} eq path) r = resources-exec rest path (resources-step a covered c eq r)
prepared-exec : ∀ {c as c′ w hid mid} → Interference as → Executes c as c′ →
  Prepared w hid mid (world c) (inboundGovernor c) → Prepared w hid mid (world c′) (inboundGovernor c′)
prepared-exec empty done p = p
prepared-exec (more {a} covered rest) (next {c = c} eq path) p = prepared-exec rest path (prepared-step a covered c eq p)
chain-exec : ∀ {c as c′ w mid} → Interference as → Executes c as c′ →
  Chain w mid (world c) (inboundGovernor c) → Chain w mid (world c′) (inboundGovernor c′)
chain-exec empty done ch = ch
chain-exec (more {a} covered rest) (next {c = c} eq path) ch = chain-exec rest path (chain-step a covered c eq ch)

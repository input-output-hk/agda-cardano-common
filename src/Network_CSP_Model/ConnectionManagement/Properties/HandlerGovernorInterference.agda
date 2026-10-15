{-# OPTIONS --guardedness #-}

-- Add all inbound-release and remote-state actions, including scored pruning.
-- This preserves reference evidence, not publication or attachment readiness.
module ConnectionManagement.Properties.HandlerGovernorInterference where

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
open import ConnectionManagement.Properties.IGTableRetention
open import ConnectionManagement.Properties.HandlerTableRetention using (retains-chain)
open import ConnectionManagement.Properties.HandlerRuntimeInterference using (resources-retained)
import ConnectionManagement.Properties.HandlerAllIGInterference as Runtime
import ConnectionManagement.Properties.ReleaseRetention as Release
import ConnectionManagement.Properties.RemoteRetention as Remote
import ConnectionManagement.Properties.IGRetention as IGEffects
import ConnectionManagement.Properties.CleanupRetention as Cleanup
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L

prepared-retained : ∀ {w hid mid s s′ ig ig′} → Cleanup.Retains s s′ → Retains ig ig′ →
  Prepared w hid mid s ig → Prepared w hid mid s′ ig′
prepared-retained {hid = hid} {mid} eff anchors p with muxesRetained anchors mid (Prepared.mx p) (Prepared.muxFound p)
... | m′ , muxFound , same = record
  { resources = resources-retained eff (Prepared.resources p)
  ; hd = Prepared.hd p; mx = m′
  ; handleFound = handlesRetained anchors hid (Prepared.hd p) (Prepared.handleFound p)
  ; handleMux = Prepared.handleMux p; muxFound = muxFound
  ; keyMatches = trans same (Prepared.keyMatches p) }

data Covered : Action → Set where
  runtime : ∀ {a} → Runtime.Covered a → Covered a
  release : ∀ {a} → Covered (releaseStep a)
  remoteOp : ∀ {a} → Covered (remoteStep a)

step-effects : ∀ a → Covered a → ∀ c {c′} → advance a c ≡ just c′ →
  Cleanup.Retains (world c) (world c′) × Retains (inboundGovernor c) (inboundGovernor c′)
step-effects a (runtime covered) c eq with Runtime.step-effects a covered c eq
... | eff , anchors = eff , anchors
step-effects .(releaseStep a) (release {a}) c eq with Release.step-effects a c eq
... | eff , anchors = eff , from-anchors anchors
step-effects .(remoteStep a) (remoteOp {a}) c eq with Remote.step-effects a c eq
... | eff , anchors = eff , from-anchors anchors

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
... | eff , anchors = retains-chain anchors (Cleanup.retains-chain eff ch)

data Interference : List Action → Set where
  empty : Interference []
  more : ∀ {a as} → Covered a → Interference as → Interference (a ∷ as)

include-runtime : ∀ {as} → Runtime.Interference as → Interference as
include-runtime Runtime.empty = empty
include-runtime (Runtime.more covered rest) = more (runtime covered) (include-runtime rest)

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

{-# OPTIONS --guardedness #-}

-- Every implemented dispatcher action retains existing reference evidence.
-- This preserves reference evidence, not publication or attachment readiness.
module ConnectionManagement.Properties.HandlerDispatcherInterference where

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
open import ConnectionManagement.Properties.HandlerStateRetention using (resources-retained)
import ConnectionManagement.Properties.HandlerStateRetention as StateChain
import ConnectionManagement.Properties.StateRetention as StateRetention
import ConnectionManagement.Properties.AdmissionRetention as Admission
import ConnectionManagement.Properties.PublicationRetention as Publication
import ConnectionManagement.Properties.HandlerAllIGInterference as AllIG
import ConnectionManagement.Properties.HandlerRuntimeInterference as Earlier
import ConnectionManagement.Properties.HandlerInterference as Caller
open import ConnectionManagement.Properties.HandlerAnchors using (anchors-refl)
import ConnectionManagement.Properties.HandlerGovernorInterference as Runtime
import ConnectionManagement.Properties.ReleaseRetention as Release
import ConnectionManagement.Properties.RemoteRetention as Remote
import ConnectionManagement.Properties.LifecycleRetention as Lifecycle
import ConnectionManagement.Properties.IGRetention as IGEffects
import ConnectionManagement.Properties.CleanupRetention as Cleanup
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L

prepared-retained : ∀ {w hid mid s s′ ig ig′} → StateRetention.Retains s s′ → Retains ig ig′ →
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
  admission : ∀ {w a} → Covered (admissionStep w a)
  publication : ∀ {w r o} → Covered (handlerPublication w r o)

step-effects : ∀ a → Covered a → ∀ c {c′} → advance a c ≡ just c′ →
  StateRetention.Retains (world c) (world c′) × Retains (inboundGovernor c) (inboundGovernor c′)
step-effects a (runtime covered) c eq with Runtime.step-effects a covered c eq
... | eff , anchors = StateRetention.from-cleanup eff , anchors
step-effects .(admissionStep w a) (admission {w} {a}) c eq with Admission.step-effects w a c eq
... | eff , refl = eff , from-anchors (anchors-refl _)

step-effects .(handlerPublication w r o) (publication {w} {r} {o}) c eq with Publication.step-effects w r o c eq
... | eff , refl = eff , from-anchors (anchors-refl _)

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
... | eff , anchors = retains-chain anchors (StateChain.retains-chain eff ch)

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

-- Exhaustive coverage removes the action-subset premise at the public endpoint.
all-actions : ∀ as → Interference as
all-actions [] = empty
all-actions (admissionStep w a ∷ as) = more admission (all-actions as)
all-actions (handlerPublication w r o ∷ as) = more publication (all-actions as)
all-actions (handlerStep w a ∷ as) = more (runtime Runtime.lifecycle) (all-actions as)
all-actions (releaseStep a ∷ as) = more (runtime Runtime.release) (all-actions as)
all-actions (remoteStep a ∷ as) = more (runtime Runtime.remoteOp) (all-actions as)
all-actions (igStep a ∷ as) = more (runtime (Runtime.runtime AllIG.ig)) (all-actions as)
all-actions (handlerExit w ∷ as) = more (runtime (Runtime.runtime (AllIG.runtime Earlier.exit))) (all-actions as)
all-actions (cleanupStep w a ∷ as) = more (runtime (Runtime.runtime (AllIG.runtime Earlier.cleanup))) (all-actions as)
all-actions (handshakeStep w a ∷ as) = more (runtime (Runtime.runtime (AllIG.runtime (Earlier.caller Caller.consumer)))) (all-actions as)

all-resources : ∀ {c as c′ w} → Executes c as c′ → Resources w (world c) → Resources w (world c′)
all-resources {as = as} = resources-exec (all-actions as)
all-prepared : ∀ {c as c′ w hid mid} → Executes c as c′ →
  Prepared w hid mid (world c) (inboundGovernor c) → Prepared w hid mid (world c′) (inboundGovernor c′)
all-prepared {as = as} = prepared-exec (all-actions as)
all-chain : ∀ {c as c′ w mid} → Executes c as c′ →
  Chain w mid (world c) (inboundGovernor c) → Chain w mid (world c′) (inboundGovernor c′)
all-chain {as = as} = chain-exec (all-actions as)

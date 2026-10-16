{-# OPTIONS --guardedness #-}

-- Another handler attaches during the delay; CM reads a result in the suffix.
module ConnectionManagement.Negative.RegistryAttachment where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Store using (put)
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.Handshake as H
open import ConnectionManagement.Rules.OriginMonitor using (ticket)
open import ConnectionManagement.Properties.RegistryPublication using (Sound)
open import ConnectionManagement.Properties.RegistryAttachment
open import ConnectionManagement.CSP.OriginRegistry using (Process; trace-intro)
open import ConnectionManagement.CSP.RegistryAttachment
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
import ConnectionManagement.CSP.RegistryAdmission as A
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.CSP.HandlerLifecycle using (cancelError)
import ConnectionManagement.Negative.RegistryPublication as Publication
open import ConnectionManagement.Scenarios.Admission using (child₀; child₁; w₀; r₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

firstAttached bothAttached consumed : State
firstAttached = registry (record (machine A.s18)
  { handlerLifecycles = (child₀ , L.frame (ident 0) cancelError L.monitoring) ∷ [] }) (entries A.s18)
bothAttached = registry (record (machine A.s18)
  { handlerLifecycles = (child₀ , L.frame (ident 0) cancelError L.monitoring) ∷
      (child₁ , L.frame (ident 1) cancelError L.monitoring) ∷ [] }) (entries A.s18)
consumed = registry (record (machine bothAttached) { world = record (Open.world (machine bothAttached))
  { admissions = put w₀ (S.admissionWorker r₀ (S.commitHandshake (ident 0) (S.negotiated (ident 0) duplex)))
      (S.admissions (Open.world (machine bothAttached))) } }) (entries A.s18)

before after : List Action
before = A.publication₁ ∷ attachment child₀ cancelError ∷ []
after = dispatch (Open.handshakeStep w₀ H.readResult) ∷ []
waiting : Executes A.s17 before firstAttached
waiting = next {s₁ = A.s18} refl (next refl done)
suffix : Executes bothAttached after consumed
suffix = next refl done

result : Σ (Sound child₁ (ident 1) duplex A.s16 A.s17)
  (λ certificate → Attached child₁ (ident 1) (Sound.ticket certificate) duplex (machine consumed))
result = publication-attachment child₁ (ident 1) duplex cancelError
  A.allocation-prefix Publication.allocation-supported refl waiting refl suffix

-- The observable continuation contains both the delay and a nonempty suffix.
continuation : Executes A.s16
  (A.publication₂ ∷ A.publication₁ ∷ attachment child₀ cancelError ∷ attachment child₁ cancelError ∷ after) consumed
continuation = next {s₁ = A.s17} refl (next {s₁ = A.s18} refl
  (next {s₁ = firstAttached} refl (next {s₁ = bothAttached} refl suffix)))
continuation-trace : traces (Process A.s16)
  (map label (A.publication₂ ∷ A.publication₁ ∷ attachment child₀ cancelError ∷ attachment child₁ cancelError ∷ after))
continuation-trace = trace-intro continuation

-- A certificate naming the other handler's mux contradicts the actual frame.
no-wrong-mux : ¬ Attached child₁ (ident 1) (ticket (ident 0) (G.proto ∷ []) duplex) duplex (machine consumed)
no-wrong-mux certificate with trans
  (cong L.capturedMux (just-injective (Attached.frameFound certificate))) (Attached.captured certificate)
... | ()

-- Attachment success remains a premise: the already-attached worker cannot
-- attach again, even though its origin and tracked references still exist.
reattach-refused : step (attachment child₁ cancelError) consumed ≡ nothing
reattach-refused = refl

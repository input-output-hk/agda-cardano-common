{-# OPTIONS --guardedness #-}

-- Every IG action, plus earlier runtime interference, before attachment.
module ConnectionManagement.CSP.HandlerAllIGInterference where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerEstablishment
open import ConnectionManagement.Properties.HandlerAllIGInterference
open import ConnectionManagement.Properties.HandlerConsumerEffects using (ParentAction)
import ConnectionManagement.Properties.HandlerConsumerEffects as Effects
open import ConnectionManagement.Properties.HandlerReferences using (Chain; TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement using (all-exec-preserves)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; cancelError)
import ConnectionManagement.CSP.HandlerEstablishment as Establish
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀; key₀)
open import ConnectionManagement.Scenarios.Handshake using (success; info)
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-resources : ∀ {c as P w} → Interference as → Resources w (world c) →
  Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Resources w (world c′))
raw-resources covered r reach with exec-inv reach
... | c′ , same , path = c′ , same , resources-exec covered path r

raw-prepared : ∀ {c as P w hid mid} → Interference as → Prepared w hid mid (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Prepared w hid mid (world c′) (inboundGovernor c′))
raw-prepared covered p reach with exec-inv reach
... | c′ , same , path = c′ , same , prepared-exec covered path p

-- Interference lists are restricted; the suffix after attachment is arbitrary.
raw-delayed-attachment : ∀ {w hid mid c P} flow err before after suffix →
  Interference before → Interference after → Prepared w hid mid (world c) (inboundGovernor c) →
  Process c ⟹⟨ map label (before ++
    (handlerPublication w (negotiated hid flow) resultWritten ∷
      (after ++ (handlerStep w (L.attach err) ∷ suffix)))) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-delayed-attachment {w} {hid} {mid} flow err before after suffix beforeCovered afterCovered prepared reach
  with exec-inv reach
... | c′ , same , path with exec-split before path
...   | c₁ , beforePath , next {c₁ = c₂} published rest with exec-split after rest
...     | c₃ , afterPath , next attached suffixPath = c′ , same ,
  all-exec-preserves suffixPath w (attach-established w err c₃
    (chain-exec afterCovered afterPath
      (publication-creates w hid mid flow c₁ (prepared-exec beforeCovered beforePath prepared) published)) attached)

import ConnectionManagement.CSP.HandlerInterference as Caller
import ConnectionManagement.CSP.HandlerIGBoundary as Boundary
import ConnectionManagement.CSP.HandlerIGInterference as LoopProof
import ConnectionManagement.Rules.MuxRuntime as M
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.IGTableRetention using (from-anchors)
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors)
import ConnectionManagement.Properties.CleanupRetention as Cleanup

-- Allocate unrelated references before the original handler publishes its result.
added : Configuration
added = record Caller.waiting { inboundGovernor = record (inboundGovernor Caller.waiting)
  { execution = record (IG.execution (inboundGovernor Caller.waiting))
    { handles = put Boundary.newHandle (M.handleState Boundary.newMux (G.proto ∷ []) duplex)
        (IG.handles (IG.execution (inboundGovernor Caller.waiting)))
    ; muxes = put Boundary.newMux Boundary.installedMux
        (IG.muxes (IG.execution (inboundGovernor Caller.waiting))) } } }
installation-path : Executes Caller.waiting (igStep Boundary.installAction ∷ []) added
installation-path = next refl done
added-prepared : Prepared child₀ (ident 0) G.mid (world added) (inboundGovernor added)
added-prepared = prepared-exec (more ig empty) installation-path Caller.waiting-prepared
installation-csp : Process Caller.waiting ⟹⟨ map label (igStep Boundary.installAction ∷ []) ⟩ Process added
installation-csp = exec-intro installation-path
new-handle-present : lookup Boundary.newHandle (IG.handles (IG.execution (inboundGovernor added))) ≡
  just (M.handleState Boundary.newMux (G.proto ∷ []) duplex)
new-handle-present = refl

-- Matched publication and attachment can follow table growth. These remain
-- successful-step premises in the general theorem, not consequences of retention.
published attached : Configuration
published = record Caller.published { inboundGovernor = inboundGovernor added }
attached = tracked L.monitoring published
schedule : List Action
schedule = igStep Boundary.installAction ∷ handlerPublication child₀ success resultWritten ∷
  handlerStep child₀ (L.attach cancelError) ∷ []
schedule-path : Executes Caller.waiting schedule attached
schedule-path = next {c₁ = added} refl (next {c₁ = published} refl (next refl done))
schedule-csp : Process Caller.waiting ⟹⟨ map label schedule ⟩ Process attached
schedule-csp = exec-intro schedule-path
attached-chain : TrackedChain child₀ attached
attached-chain = attach-established child₀ cancelError published
  (publication-creates child₀ (ident 0) G.mid duplex added added-prepared refl) refl
schedule-reachable : Σ Configuration (λ c′ → Process attached ≡ Process c′ × TrackedChain child₀ c′)
schedule-reachable = raw-delayed-attachment duplex cancelError
  (igStep Boundary.installAction ∷ []) [] [] (more ig empty) empty Caller.waiting-prepared schedule-csp

-- Local pending-decision fixture: publishing the captured empty membership
-- removes a registration while retaining the installed handle and mux.
-- No whole-admission reachability claim is made for this pending continuation.
decisionInput decisionOutput : Configuration
decisionInput = record G.registered { inboundGovernor =
  IG.setPC (IG.publishDecision 10 [] IG.emptyPublished) (inboundGovernor G.registered) }
decisionOutput = record G.registered { inboundGovernor = record (inboundGovernor G.registered)
  { publishedState = IG.emptyPublished; continuation = IG.readNext 10 [] } }
decision-input-prepared : Prepared child₀ (ident 0) G.mid (world decisionInput) (inboundGovernor decisionInput)
decision-input-prepared = prepared-retained (Cleanup.retains refl refl (λ _ p → p) (λ _ p → p))
  (from-anchors (record { handlesSame = refl; muxesRetained = λ mid m found → m , found , refl }))
  LoopProof.registered-prepared
decision-path : Executes decisionInput (igStep IG.commitDecision ∷ []) decisionOutput
decision-path = next refl done
decision-prepared : Prepared child₀ (ident 0) G.mid (world decisionOutput) (inboundGovernor decisionOutput)
decision-prepared = prepared-exec (more ig empty) decision-path decision-input-prepared
decision-csp : Process decisionInput ⟹⟨ map label (igStep IG.commitDecision ∷ []) ⟩ Process decisionOutput
decision-csp = exec-intro decision-path
registration-removed : lookup key₀ (IG.connections (IG.publishedState (inboundGovernor decisionOutput))) ≡ nothing
registration-removed = refl
decision-unattached : handlerLifecycles decisionOutput ≡ []
decision-unattached = refl

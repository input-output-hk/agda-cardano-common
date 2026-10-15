{-# OPTIONS --guardedness #-}

-- Successful abstract boundaries do not by themselves enforce key coherence.
module ConnectionManagement.Negative.HandlerEstablishment where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerEstablishment using (chain-premises)
import ConnectionManagement.Properties.HandlerAttachment as Attachment
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro; refused-extension)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; cancelError)
open import ConnectionManagement.CSP.HandlerEstablishment using (forked; installed; prefix; prefix-path)
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀; key₁)
open import ConnectionManagement.Scenarios.Handshake using (success)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.MuxRuntime as M
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_; traces)

wrongMux : M.Mux
wrongMux = record G.newMux { key = key₁ }
wrongInstalled wrongPublished wrongAttached : Configuration
wrongInstalled = record installed { inboundGovernor = IG.setMux G.mid wrongMux (inboundGovernor installed) }
wrongPublished = record wrongInstalled { world = record (world wrongInstalled) { handshakeResults = F.resultStore } }
wrongAttached = tracked L.monitoring wrongPublished
wrongActions : List Action
wrongActions = igStep (IG.installHandle (ident 0) G.mid key₁ (G.proto ∷ []) duplex) ∷
  handlerPublication child₀ success resultWritten ∷ handlerStep child₀ (L.attach cancelError) ∷ []
wrong-path : Executes forked wrongActions wrongAttached
wrong-path = next {c₁ = wrongInstalled} refl (next {c₁ = wrongPublished} refl (next refl done))
wrong-csp : Process forked ⟹⟨ map label wrongActions ⟩ Process wrongAttached
wrong-csp = exec-intro wrong-path

-- Attachment accepted, but the model trace has no coherent tracked chain.
no-wrong-chain : ¬ TrackedChain child₀ wrongAttached
no-wrong-chain (f , frameFound , ch) = case
  Attachment.coherent (chain-premises ch)
    (handlerStart (ident 0) (ident 0) (ident 0) key₀) (ident 0) duplex
    (M.handleState G.mid (G.proto ∷ []) duplex) wrongMux refl refl refl refl of λ ()

-- Installation alone does not publish a negotiated result for attachment.
unpublished-refused : advance (handlerStep child₀ (L.attach cancelError)) installed ≡ nothing
unpublished-refused = refl
no-unpublished-attachment : ¬ traces (Process installed)
  (map label (handlerStep child₀ (L.attach cancelError) ∷ []))
no-unpublished-attachment = refused-extension {as = []} done unpublished-refused

-- The same mismatched input is reachable from the accepted-socket fixture in
-- the open model. This is not evidence that the source supplies that input.
wrong-whole-csp : Process F.start ⟹⟨ map label (prefix ++ wrongActions) ⟩ Process wrongAttached
wrong-whole-csp = exec-intro (exec-append prefix-path wrong-path)
